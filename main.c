
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <time.h>

// --------------------------- Book loading ---------------------------



// Prefer #embed (C23). Fallback to runtime file read.
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L
// With #embed we can do:
// static const char book[] = { #embed "pg84.txt", '\0' };
static const char book[] = {
#embed "pg84.txt"
, '\0'
};
static char *book_buf = NULL; // not used in this path
#else
// Fallback: read pg84.txt at runtime into book_buf.
static char *book_buf = NULL;
static const char *book = NULL;

static void load_book_from_disk(void) {
  const char *fname = "pg84.txt";
  FILE *f = fopen(fname, "rb");
  if (!f) {
    fprintf(stderr, "Error: could not open %s. Put pg84.txt next to the program.\n", fname);
    exit(1);
  }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  if (n < 0) { perror("ftell"); exit(1); }
  fseek(f, 0, SEEK_SET);
  book_buf = (char *)malloc((size_t)n + 1);
  if (!book_buf) { fprintf(stderr, "OOM\n"); exit(1); }
  size_t r = fread(book_buf, 1, (size_t)n, f);
  fclose(f);
  book_buf[r] = '\0';
  book = book_buf;
}
#endif

// We will mutate the book during tokenization, so cast away const safely into a writable copy.
static char *book_mut = NULL;

// Replace non-printable characters with spaces (keeps punctuation intact).
static void replace_non_printable_chars_with_space(void) {
  for (size_t i = 0; book_mut[i] != '\0'; ++i) {
    unsigned char c = (unsigned char)book_mut[i];
    if (!isprint(c)) book_mut[i] = ' ';
  }
}

// --------------------------- Token & successors ---------------------------

// Upper bounds are guided by the novel size; we’ll grow dynamically where needed.
#define HASH_SIZE 524287          // large-ish prime for open addressing
#define INIT_SUCC_CAP 4

static char **tokens = NULL;       // tokens[id] -> pointer into book_mut
static size_t tokens_size = 0;
static size_t tokens_cap = 0;

static int *hash_index = NULL;     // hash table storing token ids (or -1 if empty)

// For each token id, we store a dynamic array of successor pointers:
static char ***succs = NULL;       // succs[id] -> array of char* (successor tokens)
static size_t *succs_sizes = NULL; // count of successors for token id
static size_t *succs_caps = NULL;  // capacity of successor array for token id

static void ensure_tokens_capacity(void) {
  if (tokens_size >= tokens_cap) {
    size_t new_cap = tokens_cap ? tokens_cap * 2 : 32768;
    tokens = (char **)realloc(tokens, new_cap * sizeof(char *));
    succs = (char ***)realloc(succs, new_cap * sizeof(char **));
    succs_sizes = (size_t *)realloc(succs_sizes, new_cap * sizeof(size_t));
    succs_caps  = (size_t *)realloc(succs_caps,  new_cap * sizeof(size_t));
    if (!tokens || !succs || !succs_sizes || !succs_caps) { fprintf(stderr, "OOM\n"); exit(1); }
    // Initialize new ranges
    for (size_t i = tokens_cap; i < new_cap; ++i) {
      succs[i] = NULL;
      succs_sizes[i] = 0;
      succs_caps[i] = 0;
    }
    tokens_cap = new_cap;
  }
}

static unsigned long hash_str(const char *s) {
  // djb2 variant
  unsigned long h = 5381UL;
  int c;
  while ((c = (unsigned char)*s++)) {
    h = ((h << 5) + h) ^ (unsigned long)c;
  }
  return h;
}

static void hash_init(void) {
  hash_index = (int *)malloc(HASH_SIZE * sizeof(int));
  if (!hash_index) { fprintf(stderr, "OOM\n"); exit(1); }
  for (size_t i = 0; i < HASH_SIZE; ++i) hash_index[i] = -1;
}

static int hash_find(const char *s) {
  unsigned long h = hash_str(s) % HASH_SIZE;
  for (size_t probe = 0; probe < HASH_SIZE; ++probe) {
    size_t i = (h + probe) % HASH_SIZE;
    int id = hash_index[i];
    if (id == -1) return -1;            // empty
    if (tokens[id] && strcmp(tokens[id], s) == 0) return id;
  }
  return -1; // table full (shouldn’t happen)
}

static void hash_insert(const char *s, int id) {
  unsigned long h = hash_str(s) % HASH_SIZE;
  for (size_t probe = 0; probe < HASH_SIZE; ++probe) {
    size_t i = (h + probe) % HASH_SIZE;
    if (hash_index[i] == -1) {
      hash_index[i] = id;
      return;
    }
  }
  fprintf(stderr, "Hash table full\n");
  exit(1);
}

// Returns id for token, creating a new id if needed.
static size_t token_id(const char *tok) {
  int found = hash_find(tok);
  if (found >= 0) return (size_t)found;

  ensure_tokens_capacity();
  size_t id = tokens_size++;
  tokens[id] = (char *)tok;

  // initialize successor lists for this id
  succs[id] = NULL;
  succs_sizes[id] = 0;
  succs_caps[id] = 0;

  hash_insert(tok, (int)id);
  return id;
}

static void append_to_succs(const char *prev, const char *curr) {
  size_t pid = token_id(prev);
  // We store successor POINTERS (curr points into book_mut)
  if (succs_caps[pid] == 0) {
    succs_caps[pid] = INIT_SUCC_CAP;
    succs[pid] = (char **)malloc(succs_caps[pid] * sizeof(char *));
    if (!succs[pid]) { fprintf(stderr, "OOM\n"); exit(1); }
  } else if (succs_sizes[pid] >= succs_caps[pid]) {
    succs_caps[pid] *= 2;
    succs[pid] = (char **)realloc(succs[pid], succs_caps[pid] * sizeof(char *));
    if (!succs[pid]) { fprintf(stderr, "OOM\n"); exit(1); }
  }
  succs[pid][succs_sizes[pid]++] = (char *)curr;
}

// --------------------------- Tokenization ---------------------------

static void tokenize_and_fill_succs(char *delimiters, char *str) {
  // Reset sizes (safe even on first call as we malloc zeros via ensure)
  // We don't clear tokens table here; token_id grows as we encounter new tokens.
  char *saveptr = NULL;
  char *prev = NULL;
  char *tok = strtok_r(str, delimiters, &saveptr);
  while (tok) {
    token_id(tok);
    if (prev) append_to_succs(prev, tok);
    prev = tok;
    tok = strtok_r(NULL, delimiters, &saveptr);
  }
}

// --------------------------- Sentence generation ---------------------------

static char last_char(const char *s) {
  size_t n = strlen(s);
  return n ? s[n - 1] : '\0';
}

static bool token_ends_a_sentence(const char *token) {
  char c = last_char(token);
  return c == '.' || c == '?' || c == '!';
}

static size_t random_token_id_that_starts_a_sentence(void) {
  // Try random picks first
  for (int attempts = 0; attempts < 10000; ++attempts) {
    if (tokens_size == 0) break;
    size_t i = (size_t)(rand() % (int)tokens_size);
    unsigned char c0 = (unsigned char)tokens[i][0];
    if (isalpha(c0) && isupper(c0)) return i;
  }
  // Fallback: first capitalized token
  for (size_t i = 0; i < tokens_size; ++i) {
    unsigned char c0 = (unsigned char)tokens[i][0];
    if (isalpha(c0) && isupper(c0)) return i;
  }
  return 0;
}

static char *generate_sentence(char *out, size_t out_size) {
  if (out_size == 0) return out;
  out[0] = '\0';

  size_t start_id = random_token_id_that_starts_a_sentence();
  const char *token = tokens_size ? tokens[start_id] : "";
  strncat(out, token, out_size - 1);
  if (token_ends_a_sentence(token)) return out;

  while (strlen(out) + 2 < out_size) {
    size_t curr_id = token_id(token);
    size_t nsucc = succs_sizes[curr_id];
    if (nsucc == 0) break; // dead end

    const char *next = succs[curr_id][rand() % nsucc];

    size_t need = strlen(out) + 1 + strlen(next) + 1;
    if (need >= out_size) break;

    strcat(out, " ");
    strcat(out, next);
    token = next;
    if (token_ends_a_sentence(token)) break;
  }
  return out;
}

static bool ends_with_char(const char *s, char c) {
  return last_char(s) == c;
}

// --------------------------- Main ---------------------------

int main(void) {
  srand((unsigned)time(NULL));

#if !(defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L)
  load_book_from_disk();
#endif

  // Make a writable copy of the book content (we’ll mutate with strtok_r).
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L
  size_t blen = strlen(book);
  book_mut = (char *)malloc(blen + 1);
  if (!book_mut) { fprintf(stderr, "OOM\n"); return 1; }
  memcpy(book_mut, book, blen + 1);
#else
  book_mut = (char *)malloc(strlen(book) + 1);
  if (!book_mut) { fprintf(stderr, "OOM\n"); return 1; }
strcpy(book_mut, book);

#endif

  replace_non_printable_chars_with_space();

  // Init structures
  hash_init();
  ensure_tokens_capacity(); // allocate initial blocks

  // Tokenize on spaces/newlines only so punctuation sticks to tokens.
  tokenize_and_fill_succs(" \n\r", book_mut);

  // Generate a question sentence and an exclamation sentence.
  // Keep sampling until the final char matches the desired punctuation.
  char buf[4096];

  // Question
  for (int tries = 0; tries < 1000; ++tries) {
    generate_sentence(buf, sizeof buf);
    if (ends_with_char(buf, '?')) {
      printf("%s\n\n", buf);
      break;
    }
  }

  // Exclamation
  for (int tries = 0; tries < 1000; ++tries) {
    generate_sentence(buf, sizeof buf);
    if (ends_with_char(buf, '!')) {
      printf("%s\n", buf);
      break;
    }
  }

  // Cleanup (optional in short-lived program)
  free(book_mut);
#if !(defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L)
  free(book_buf);
#endif
  free(hash_index);
  for (size_t i = 0; i < tokens_size; ++i) free(succs[i]);
  free(succs);
  free(succs_sizes);
  free(succs_caps);
  free(tokens);

  return 0;
}
