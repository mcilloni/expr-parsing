#define _GNU_SOURCE

#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32) 

int vasprintf(char **buf, const char *format, va_list va) {
	va_list tmp_va;
	char dummy;

	va_copy(tmp_va, va);
	int len = vsnprintf(&dummy, 0, format, tmp_va);
	va_end(tmp_va);

	if (len < 0) {
		*buf = NULL;
		return len;
	}

	// Account for null terminator 
	len += 1;
	*buf = malloc(len);
	if (!*buf)
		return -1;

	int ret = vsnprintf(*buf, len, format, va);
	if (ret < 0) {
		free(*buf);
		*buf = NULL;
	}

	return ret;
}

#define _USE_MATH_DEFINES

#endif

#include <math.h>

int nextc(FILE *f) {
  char ch;

  do {
    ch = getc(f);
  } while (isblank(ch));

  return ch;
}

int peekc(FILE *f) {
  int ret = getc(f);

  if (ret > 0) {
    ungetc(ret, f);
  }

  return ret;
}

enum tok_ty {
  TOK_DIV,
  TOK_MINUS,
  TOK_NUMBER,
  TOK_PLUS,
  TOK_TIMES,
  TOK_NEWLINE,
  TOK_OPAR,
  TOK_CPAR,
  TOK_CARET,
  TOK_ID
};

typedef int8_t op_prec_t;

op_prec_t OP_PREC[] = {
  [TOK_DIV] = 2,
  [TOK_MINUS] = 1,
  [TOK_NUMBER] = -1,
  [TOK_PLUS] = 1,
  [TOK_TIMES] = 2,
  [TOK_NEWLINE] = -1,
  [TOK_OPAR] = -1,
  [TOK_CPAR] = -1,
  [TOK_CARET] = 3,
  [TOK_ID] = -1
};

enum op_arity {
  OP_NONE = 0,
  OP_UNARY,
  OP_BINARY
};

enum op_assoc {
  ASSOC_NONE = 0,
  ASSOC_LEFT,
  ASSOC_RIGHT
};

struct tok_info {
  const char *descr;
  enum op_arity arity;
  enum op_assoc assoc;
} TOK_INFO[] = {
  [TOK_DIV] = { .arity = OP_BINARY, .assoc = ASSOC_LEFT, .descr = "/" },
  [TOK_MINUS] = { .arity = OP_BINARY, .assoc = ASSOC_LEFT, .descr = "-" },
  [TOK_NUMBER] = { .arity = OP_NONE, .assoc = ASSOC_NONE, .descr = "<number>" },
  [TOK_PLUS] = { .arity = OP_BINARY, .assoc = ASSOC_LEFT, .descr = "+" },
  [TOK_TIMES] = { .arity = OP_BINARY, .assoc = ASSOC_LEFT, .descr = "*" },
  [TOK_NEWLINE] = { .arity = OP_NONE, .assoc = ASSOC_NONE, .descr = "\\n" },
  [TOK_OPAR] = { .arity = OP_NONE, .assoc = ASSOC_NONE, .descr = "(" },
  [TOK_CPAR] = { .arity = OP_NONE, .assoc = ASSOC_NONE, .descr = ")" },
  [TOK_CARET] = { .arity = OP_BINARY, .assoc = ASSOC_RIGHT, .descr = "^" },
  [TOK_ID] = { .arity = OP_NONE, .assoc = ASSOC_NONE, .descr = "<id>" }
};

struct tok {
  enum tok_ty kind;
  union {
    double num_val; // kind == NUMBER
    char id[sizeof(double)]; // kind == ID
  };
};

int tok_dump(struct tok tok) {
  switch (tok.kind) {
    case TOK_NUMBER: 
      return printf("%g", tok.num_val);

    case TOK_ID:
      return fputs(tok.id, stdout);

    default:
      return fputs(TOK_INFO[tok.kind].descr, stdout); 
  }
}

enum lex_res {
  LEX_OK = 0,
  LEX_IO_ERR = 1,
  LEX_UNEXPECTED = 2,
  LEX_EOF = 3,
  LEX_DANGLING = 4,
  LEX_ID_TOO_LONG
};

const char *LEX_STATUS[] = {
  [LEX_OK] = "ok",
  [LEX_IO_ERR] = "i/o error",
  [LEX_UNEXPECTED] = "unexpected token",
  [LEX_EOF] = "end of file",
  [LEX_DANGLING] = "uninitialized",
  [LEX_ID_TOO_LONG] = "identifier exceeds max length (usually 7)"
};

struct lex {
  FILE *f;
  struct tok *next;
  bool eof;
};

enum lex_res lex_next_tok(struct lex *lex);

enum lex_res lex_init(struct lex *lex, FILE *f) {
  lex->f = f;
  lex->eof = false;  // preload first token
  lex->next = calloc(1, sizeof *lex->next);

  return lex_next_tok(lex);
}

void lex_invalid(struct lex *lex) {
  free(lex->next);
  lex->next = NULL;
}

void lex_deinit(struct lex *lex) {
  lex_invalid(lex);
  if (lex->f != stdin) {
    fclose(lex->f);
  }
}

enum lex_res lex_next_id_tok(struct lex *lex) {
  size_t max_id_sz = sizeof lex->next->id;
  memset(lex->next->id, 0, max_id_sz);
  
  for (size_t i = 0; i < max_id_sz - 1; ++i) {
    char peek = peekc(lex->f);

    if (peek == EOF && ferror(lex->f)) {
      return LEX_IO_ERR;
    }

    if (!isalnum(peek)) {
      break;
    }

    lex->next->id[i] = nextc(lex->f);
  }

  // Only true when we exited the loop because we got more
  // chars than we could store (and there are still alphanumeric 
  // on the stream)
  if (isalnum(peekc(lex->f))) {
    return LEX_ID_TOO_LONG; 
  }

  lex->next->kind = TOK_ID;

  return LEX_OK;
}

enum lex_res lex_next_num_tok(struct lex *lex) {
  uint64_t val = 0;
  double dec_div = 1.0;
  bool dec = false;
  
  for (;;) {
    char next = peekc(lex->f);
          
    if (next == EOF && ferror(lex->f)) {
      return LEX_IO_ERR;
    }

    if (next == '.') {
      if (dec) {
        // Two dots in a numeric token
        return LEX_UNEXPECTED;
      } else {
        dec = true;
        getc(lex->f); // drop the dot

        continue;
      }
    }

    if (isdigit(next)) {
      getc(lex->f); // discard the number we've already
      val = 10*val + (next - '0');

      if (dec) {
        dec_div *= 10;
      }
    } else {
      break;
    }
  }
    
  *lex->next = (struct tok){ .kind = TOK_NUMBER, .num_val = val / dec_div };

  return LEX_OK;
}

enum lex_res lex_next_tok(struct lex *lex) {
  char first;
  
  if ((first = nextc(lex->f)) == EOF) {
    if (ferror(lex->f)) {
      return LEX_IO_ERR;      
    }

    return LEX_EOF;
  }

  switch (first) {
    case '/':
      lex->next->kind = TOK_DIV;
      break;

    case '-':
      lex->next->kind = TOK_MINUS;
      break;

    case '+':
      lex->next->kind = TOK_PLUS;
      break;

    case '*':
      lex->next->kind = TOK_TIMES;
      break;

    case '\n':
      lex->next->kind = TOK_NEWLINE;
      break;

    case '(':
      lex->next->kind = TOK_OPAR;
      break;

    case ')':
      lex->next->kind = TOK_CPAR;
      break;

    case '^':
      lex->next->kind = TOK_CARET;
      break;

    default:
      ungetc(first, lex->f);

      if (isdigit(first) || first == '.') {
        return lex_next_num_tok(lex);
      } else if (isalpha(first)) {
        return lex_next_id_tok(lex);
      } else {
        return LEX_UNEXPECTED;
      }
  }

  return LEX_OK;
}

enum lex_res lex_next(struct lex *lex, struct tok *res_tok) {
  if (lex->eof) {
    return LEX_EOF;
  }

  if (res_tok) {
    *res_tok = *lex->next;
  }

  enum lex_res res = lex_next_tok(lex);

  if (res != LEX_OK) {
    lex_invalid(lex); 
  }

  if (res == LEX_EOF) {
    lex->eof = true;
      
    res = LEX_OK;
  } 

  return res;
}

enum const_id {
  CONST_E,
  CONST_PI
};

const char *CONST_LABELS[] = {
  [CONST_E] = "e",
  [CONST_PI] = "pi"
};

double CONST_VALUES[] = {
  [CONST_E] = M_E,
  [CONST_PI] = M_PI
};

enum func_id {
  FUNC_ATAN,
  FUNC_COS,
  FUNC_LN,
  FUNC_LOG,
  FUNC_LOG2,
  FUNC_ROUND,
  FUNC_SIN,
  FUNC_TAN
};

const char *FUNC_LABELS[] = {
  [FUNC_ATAN] = "atan",
  [FUNC_COS] = "cos",
  [FUNC_LN] = "ln",
  [FUNC_LOG] = "log",
  [FUNC_LOG2] = "log2",
  [FUNC_ROUND] = "round",
  [FUNC_SIN] = "sin",
  [FUNC_TAN] = "tan"
};

double (*FUNC_TABLE[])(double) = {
  [FUNC_ATAN] = atan,
  [FUNC_COS] = cos,
  [FUNC_LN] = log,
  [FUNC_LOG] = log10,
  [FUNC_LOG2] = log2,
  [FUNC_ROUND] = round,
  [FUNC_SIN] = sin,
  [FUNC_TAN] = tan
};

enum node_type {
  NODE_CONST,
  NODE_DIV,
  NODE_FUNC,
  NODE_MINUS,
  NODE_NEG,
  NODE_PLUS,
  NODE_POW,
  NODE_TIMES,
  NODE_VAL
};

struct node {
  enum node_type kind;

  union {
    double val;
    enum const_id c_id;
    enum func_id f_id;
  };

  struct node *left, *right;
};

void node_free(struct node *n) {
  if (n) {
    node_free(n->left);
    node_free(n->right);

    free(n);
  }
}

struct node* node_new(enum node_type kind) {
  struct node* ret = calloc(1, sizeof *ret);

  ret->kind = kind;

  return ret;
} 

struct node* node_bin_from_token(enum tok_ty kind, struct node *left, struct node *right) {
  struct node *ret = calloc(1, sizeof *ret);

  switch (kind) {
    case TOK_CARET: 
      ret->kind = NODE_POW;
      break;

    case TOK_DIV:
      ret->kind = NODE_DIV;
      break;

    case TOK_MINUS:
      ret->kind = NODE_MINUS;
      break;

    case TOK_PLUS:
      ret->kind = NODE_PLUS;
      break;

    case TOK_TIMES:
      ret->kind = NODE_TIMES;
      break;

    default:
      free(ret);
      return NULL;
  }

  ret->left = left;
  ret->right = right;

  return ret;
}

struct parse_res {
  bool ok;
  union {
    struct node *tree;
    char *error; 
  };
};

struct parse_res RES_EMPTY = { .ok = true, .tree = NULL };

char* pres_get_err(struct parse_res res) {
  return res.ok ? NULL : res.error;
}

struct node* pres_get_tree(struct parse_res res) {
  return res.ok ? res.tree : NULL;
}

struct parse_res pres_err(const char *fmt, ...) {
  va_list args;

  va_start(args, fmt);

  struct parse_res ret = { .ok = false };
  vasprintf(&ret.error, fmt, args);

  return ret;
}

struct parse_res pres_expect(const char *expect, enum tok_ty got) {
  return pres_err("expecting %s, got '%s'",expect,  TOK_INFO[got].descr);
}

struct parse_res pres_lex_err(enum lex_res lres) {
  return pres_err("%s", LEX_STATUS[lres]);
}

struct parse_res pres_ok(struct node *tree) {
  return (struct parse_res) { .ok = true, .tree = tree };
}

struct parse_res parse_expr(struct lex *lex);

struct parse_res parse_parens(struct lex *lex) {
  struct parse_res par_expr_res = parse_expr(lex);
  if (!par_expr_res.ok) {
    return par_expr_res;
  }

  struct node *par_expr = pres_get_tree(par_expr_res);

  struct tok cpar_tok;
  enum lex_res lres = lex_next(lex, &cpar_tok);
  if (lres != LEX_OK) {
    node_free(par_expr);
 
    return pres_lex_err(lres);
  }

  if (cpar_tok.kind != TOK_CPAR) {
    node_free(par_expr);

    return pres_expect("')'", cpar_tok.kind);
  }

  return pres_ok(par_expr); 
}

struct parse_res parse_primary(struct lex *lex);

struct parse_res parse_func(struct lex *lex, const char *id) {
  enum func_id f_id;

  long long func_labels_len = (sizeof FUNC_LABELS) / (sizeof *FUNC_LABELS);
  for (f_id = 0; f_id < func_labels_len; ++f_id ) {
    if (!strcmp(id, FUNC_LABELS[f_id])) {
      break;
    }
  }

  if (f_id >= func_labels_len) {
    return pres_err("unknown function `%s`", id);
  }
 
  // We know for sure lex->next is a parenthesis, therefore
  // parse_primary will slurp it, parse everything inside and slurp the
  // final `)`
  struct parse_res call_res = parse_primary(lex);
  if (!call_res.ok) {
    return call_res;
  }

  struct node *call = pres_get_tree(call_res);

  struct node *ret = node_new(NODE_FUNC);

  ret->f_id = f_id;
  ret->left = call;

  return pres_ok(ret);
}

struct parse_res parse_primary(struct lex *lex) {
  struct tok ntok;
  enum lex_res lres = lex_next(lex, &ntok);

  if (lres == LEX_EOF) {
    return pres_err("unexpected EOF"); 
  }
      
  if (lres != LEX_OK) {
    return pres_lex_err(lres);
  }

  switch (ntok.kind) {
    case TOK_ID: {
      if (lex->next && lex->next->kind == TOK_OPAR) {
        return parse_func(lex, ntok.id);
      }

      long long const_labels_len = (sizeof CONST_LABELS) / (sizeof *CONST_LABELS);
      for (enum const_id c_id = 0; c_id < const_labels_len; ++c_id ) {
        if (!strcmp(ntok.id, CONST_LABELS[c_id])) {
          struct node *num = node_new(NODE_CONST);
          num->c_id = c_id;

          return pres_ok(num);
        }
      }

      return pres_err("unknown identifier `%s`", ntok.id);
    }

    case TOK_NUMBER: {
      struct node *num = node_new(NODE_VAL);
      num->val = ntok.num_val;

      return pres_ok(num);
    }

    case TOK_OPAR: 
      return parse_parens(lex);

    default:
      return pres_expect("a number or parentheses", ntok.kind);
  }  
}

struct parse_res parse_unary(struct lex *lex);

struct parse_res parse_binary(struct lex *lex, struct node *lhs, op_prec_t min_prec) {
  op_prec_t cur_op_prec;
  struct node *rhs = NULL;

  while (lex->next && (cur_op_prec = OP_PREC[lex->next->kind]) >= min_prec && TOK_INFO[lex->next->kind].arity == OP_BINARY) {
    struct tok op_tok;
    
    enum lex_res lres = lex_next(lex, &op_tok);
    if (lres != LEX_OK) {
      return pres_lex_err(lres);
    }

    struct parse_res rhs_res = parse_unary(lex);
    if (!rhs_res.ok) {
      return rhs_res;
    }

    rhs = pres_get_tree(rhs_res);

    if (lex->next) {
      op_prec_t next_op_prec = OP_PREC[lex->next->kind];
      bool next_assoc_right = TOK_INFO[lex->next->kind].assoc == ASSOC_RIGHT;

      if (next_op_prec > cur_op_prec || (next_assoc_right && next_op_prec == cur_op_prec)) {
        rhs_res = parse_binary(lex, rhs, next_op_prec);
        if (!rhs_res.ok) {
          return rhs_res;
        }
        
        rhs = pres_get_tree(rhs_res);
      }
    } 
 
    lhs = node_bin_from_token(op_tok.kind, lhs, rhs);
  }

  return pres_ok(lhs);
}

struct parse_res parse_unary(struct lex *lex) {
  if (lex->next && (lex->next->kind == TOK_MINUS || lex->next->kind == TOK_PLUS)) {
    struct tok op_top;
    enum lex_res lres = lex_next(lex, &op_top);
    if (lres != LEX_OK) {
      return pres_lex_err(lres); 
    }     

    struct parse_res right_expr_res = parse_unary(lex);

    if (!right_expr_res.ok) {
      return right_expr_res;
    }

    struct node *right_expr = pres_get_tree(right_expr_res);

    if (op_top.kind == TOK_MINUS) {
      if (right_expr->kind != NODE_VAL) {
        struct node *neg_expr = node_new(NODE_NEG);
        neg_expr->left = right_expr;

        return pres_ok(neg_expr);
      } else {
       right_expr->val = -right_expr->val;
      }
    } 

    return pres_ok(right_expr);
  } else {
    return parse_primary(lex);
  }
}

struct parse_res parse_expr(struct lex *lex) {
  if (!lex->next || lex->next->kind == TOK_NEWLINE) {
    return RES_EMPTY;
  }

  struct parse_res res = parse_unary(lex);

  if (pres_get_err(res)) {
    return res;
  }

  struct node *lhs = pres_get_tree(res);

  return parse_binary(lex, lhs, -1);
}

void node_dump_padded(struct node *node, uint8_t padding, bool arrow) {
  if (!node) {
    return;
  }

  for (uint8_t i = 0; i < padding; ++i) { 
    putchar(' '); 
  }

  if (arrow) {
    // Sorry Windows, no fancy UTF-8 for you
    #if defined(_WIN32) 
      fputs("--> ", stdout);
    #else
      fputs(u8"└─→ ", stdout);
    #endif
  }

  switch (node->kind) {
    case NODE_CONST:
      fputs(CONST_LABELS[node->c_id], stdout);
      break;

    case NODE_DIV:
      putchar('/');
      break;
      
    case NODE_FUNC:
      fputs(FUNC_LABELS[node->f_id], stdout);
      break;

    case NODE_MINUS:
      putchar('-');
      break;

    case NODE_NEG:
      fputs("- (neg)", stdout);
      break;

    case NODE_PLUS:
      putchar('+');
      break;

    case NODE_POW:
      putchar('^');
      break;

    case NODE_TIMES:
      putchar('*');
      break;
      
    case NODE_VAL:
      printf("%g", node->val);
      break;
  }

  putchar('\n');

  node_dump_padded(node->left, padding + 2, true);
  node_dump_padded(node->right, padding + 2, true);
}

#define node_dump(X) node_dump_padded(X, 0, false)

double eval_node(struct node *node) {
  if (!node) {
    return NAN;
  }

  double left = eval_node(node->left);
  double right = eval_node(node->right);

  switch (node->kind) {
    case NODE_CONST:
      return CONST_VALUES[node->c_id];

    case NODE_DIV: 
      return left / right;

    case NODE_FUNC:
      return FUNC_TABLE[node->f_id](left);

    case NODE_MINUS:
      return left - right;

    case NODE_NEG:
      return -left;

    case NODE_PLUS:
      return left + right;

    case NODE_POW:
      return pow(left, right);

    case NODE_TIMES:
      return left * right;

    case NODE_VAL:
      return node->val;
  }
}

void print_help(const char *progname) {
  fprintf(stderr, "USAGE: %s [-t]\n\n", progname);
  fputs("A poor way to evaluate expressions\n", stderr);
}

int main(int argc, char *argv[]) {
  bool print_node = false;
  int status = EXIT_SUCCESS;
  
  switch (argc) {
    case 1:
      break;

    case 2:
      if (!strcmp(argv[1], "-t")) { 
        print_node = true;
        break;
      }

      if (strcmp(argv[1], "-h")) {
        fprintf(stderr, "error: unknown parameter '%s'\n", argv[1]);
        status = EXIT_FAILURE;
      }

    default:
      print_help(*argv);

      return status;
  }

  struct lex lex;

  enum lex_res lres = lex_init(&lex, stdin);
  if (lres != LEX_OK) {
    fprintf(stderr, "error: %s\n", LEX_STATUS[lres]);

    return EXIT_FAILURE; 
  }

  for (;;) {
    struct parse_res pres = parse_expr(&lex);

    if (pres.ok) {
      struct node *tree = pres_get_tree(pres);

      double res = eval_node(tree);

      // eval_node(NULL) (i.e. empty expression) always returns NaN. 
      // Avoid printing it (it's probably because someone has typed ctrl+d)
      if (tree) {
        if (print_node) {
          puts("\nTree:\n");
          node_dump(tree);
          putchar('\n');
        }

        printf("%g\n", res);
      }

      node_free(tree);

      struct tok ntok;
      lres = lex_next(&lex, &ntok);

      switch(lres) {
        case LEX_OK:
          if (ntok.kind != TOK_NEWLINE) {
            fprintf(stderr, "error: stray `%s` left in stream after expression\n", TOK_INFO[ntok.kind].descr);
            status = EXIT_FAILURE;

            goto out;
          }

	  status = EXIT_SUCCESS;
          break;

        case LEX_EOF:
          goto out;

        default:
          fprintf(stderr, "error: %s\n", LEX_STATUS[lres]);
          status = EXIT_FAILURE;
	  break;
      }
    } else {
      char *err = pres_get_err(pres);

      fprintf(stderr, "error: %s\n", err);

      free(err);

      status = EXIT_FAILURE;
    }
  }

out:
  lex_deinit(&lex);

  return status;
}
