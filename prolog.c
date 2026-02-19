/* TODO:
 * - Implement parser
 *   - Special parser arena, no frees
 * - Mention; CPP program, Microsoft Prolog Driver Paper, GP A* search
 *   for games, how prolog should be a library (you do not need language
 *   features, just libraries).
 * - We could get away with using fewer types, most things can be
 *   treated as a cons list
 * - Some more complex expressions fail, more testing is needed.
 * - Valgrind, AI/LLM code review, ...
 * - Garbage collection; make multiple versions (non-portable mark
 *   and sweep, mark and sweep, arena based).
 * - Add operators (cut, not, '_', equal, not-equal, input (read expression), output).
 * - Unit tests? Error handling
 * - Replace recursion with iteration where possible.
 * - Documentation
 * - Make sure variable is not reused between rules / can be different
 * - Debug variable names and print out id number
 * - Optimizations (mainly around memory usage, not speed).
 * - Code generation, string interning, optimizations
 * - Make a command prompt
 * - Make more test programs; successor arithmetic, grandparent <-> parent <-> child
 * - The grammar "a(X)?" is much nicer than "?a(X).", it should be added.
 * - Turn into header only library 
 * - Internally the program needs restructuring, especially around
 *   the grammar and parser. We could also use a pl_list_t type to
 *   replace some of the types used.
 * - References:
 * <https://www.cl.cam.ac.uk/~am21/papers/wflp00.pdf>
 * <https://www.cl.cam.ac.uk/~am21/research/funnel/prolog2020.cpp>
 */
/* Copyright (C) 2026 by Richard James Howe <howe.r.j.89@gmail.com>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */
#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define PL_AUTHOR  "Richard James Howe"
#define PL_LICENSE "0BSD"
#define PL_EMAIL   "howe.r.j.89@gmail.com"
#define PL_REPO    "https://github.com/howerj/prolog"
#define PL_VERSION "v0.0.1"

#define never() assert(0)
#define implies(P, Q) assert((!(P)) || (Q))
#define mutual(P, Q) do { implies(P, Q); implies(Q, P); } while (0)
#define nullable(X) /* used to indicate an argument is can be null */

#ifndef NELEMS
#define NELEMS(X) (sizeof (X) / sizeof ((X)[0]))
#endif

#define PL_MARK (0x80u)
#define PL_TYPE_MSK (0xFu)

#ifndef PL_GC_THRESHOLD_BYTES /* we could make this scale to the size of the `stack` or `gc` fields */
#define PL_GC_THRESHOLD_BYTES (1 << 16)
#endif

struct pl_term;
struct pl_term_var_mapping;
struct pl_program;
struct pl_goal;
struct pl_clause;
struct pl_trail;

typedef struct pl_term pl_term_t;
typedef struct pl_trail pl_trail_t;
typedef struct pl_goal pl_goal_t;
typedef struct pl_program pl_program_t;
typedef struct pl_term_var_mapping pl_term_var_mapping_t;
typedef pl_goal_t pl_clause_t;

typedef uintptr_t pl_flags_t;
enum { PL_CONS, PL_VAR, PL_ATOM, PL_CLAUSE, PL_GOAL, PL_TRAIL, PL_PROGRAM, PL_TVM, }; 
typedef struct { pl_flags_t flags; char *name; } pl_atom_t; 
typedef struct { pl_flags_t flags; pl_atom_t *fsym; pl_term_t **args; size_t arity; } pl_term_cons_t;
typedef struct { pl_flags_t flags; pl_term_t *instance; int varno; } pl_term_var_t;
struct pl_term { pl_flags_t flags; union { pl_term_cons_t cons; pl_term_var_t var; } t; };
struct pl_goal { pl_flags_t flags; /*pl_term_cons_t*/pl_term_t *car; pl_goal_t *cdr; };
struct pl_trail { pl_flags_t flags; /*pl_term_var_t*/pl_term_t *car; pl_trail_t *cdr; };
struct pl_program { pl_flags_t flags; pl_clause_t *car; pl_program_t *cdr; };
struct pl_term_var_mapping { pl_flags_t flags; pl_term_var_mapping_t *parent; pl_term_t **var; char **name; size_t length; };
typedef struct { void *ptr; uintptr_t type; } pl_gc_t;
typedef struct { uint8_t *buf; size_t used, length; int ungetc; } pl_lexer_t;

enum { /* These are the parser tokens, there are only a few. */
	PLEX_LPAR  = '(', PLEX_RPAR = ')', PLEX_IS   = '=', 
	PLEX_COMMA = ',', PLEX_ATOM = 'A', PLEX_VAR  = 'V', 
	PLEX_QUERY = '?', PLEX_DOT  = '.', PLEX_EOF  = 'E', 
	PLEX_ERROR = -1,
};

typedef struct {
	pl_lexer_t lex;   /* lexer state */
	int sym;          /* currently lexed symbol */
	void *(*alloc)(void *arena, void *ptr, size_t old_sz, size_t new_sz); /* custom memory allocator function */
	void *arena;     /* passed to `alloc` */
	pl_gc_t *gc;     /* list of items that the garbage collector keeps track of */
	pl_gc_t *stack;  /* a stack of recently allocated members */
	size_t gc_used,  /* number of elements of `gc` that are used */
	       gc_size,  /* size of `gc` */
	       gc_stk_idx,  /* index into `stack` */
	       gc_stk_size, /* size of `stack` */
	       gc_bytes_since_last_gc; /* counter of bytes allocated, used to determine when to GC */
	int (*get)(void *in); /* get a character of input */
	int (*put)(void *out, int ch); /* output a character of output */
	void *in, *out;    /* `in` and `out` passed to `get` and `put` */
	long varno;        /* global variable number counter */
	int fatal;         /* error number */
	int maxlevel;      /* 0 to disable */
	unsigned sysflags; /* various control flags */
	pl_trail_t *sofar; /* used in trail, undo */
	pl_program_t *db, *tail;  /* database of facts, rules, etcetera */
	pl_goal_t *goal; /* current root level goal being run */
	pl_term_var_mapping_t *map; /* current term-var scope */
	const char *prompt; /* used for Read-Evaluate loop, a prompt to display per command line entry */
	uint8_t buf[256]; /* used for printing */
} prolog_t; /* prolog - state of the world. */

enum {
	PL_SFLAG_GC_OFF_E                = 1 << 0u, /* turn garbage collector off */
	PL_SFLAG_PRINT_ONLY_MATCHES      = 1 << 1u, /* turn most output off apart from matches */
	PL_SFLAG_ONLY_PRINT_YES_ON_MATCH = 1 << 2u, /* only print `yes` on match, no var mapping */
	PL_SFLAG_REVERSE_PROGRAM_ORDER   = 1 << 3u, /* reverse program order, this affects finding solutions! */
	PL_SFLAG_PARSER_DEBUG            = 1 << 4u, /* print out symbols for debugging purposes in parser */
};

enum {
	PL_ERROR_OK_E            =  0, /* no error */
	PL_ERROR_GENERIC_E       = -1, /* generic error; not used */
	PL_ERROR_OUT_OF_MEMORY_E = -2, /* oh no! */
	PL_ERROR_OUTPUT_E        = -3, /* any output error */
};

static inline int pl_error(prolog_t *p, const int error) {
	assert(p);
	if (!p->fatal)
		p->fatal = error;
	return p->fatal;
}

static int pl_ungetc(prolog_t *p, const int ch) {
	assert(p);
	const int r = p->lex.ungetc;
	if (r >= 0)
		return -1;
	p->lex.ungetc = ch;
	return ch;
}

static int pl_get(prolog_t *p) {
	assert(p);
	assert(p->get);
	const int r = p->lex.ungetc;
	if (r >= 0) {
		p->lex.ungetc = -1;
		return r;
	}
	return p->get(p->in);
}

static int pl_put(prolog_t *p, const int ch) {
	assert(p);
	assert(p->put);
	const int r = p->put(p->out, ch);
	if (r < 0)
		return pl_error(p, PL_ERROR_OUTPUT_E);
	return pl_error(p, 0);
}

static int pl_puts(prolog_t *p, const char *s) {
	assert(p);
	assert(s);
	int ch = 0;
	for (size_t i = 0; (ch = s[i]); i++)
		if (p->put(p->out, ch) < 0)
			return pl_error(p, PL_ERROR_OUTPUT_E);
	return pl_error(p, 0);
}

static int pl_putf(prolog_t *p, uint8_t *buf, const size_t blen, const char *fmt, ...) {
	assert(p);
	assert(buf);
	assert(fmt);
	int ch = 0;
	va_list ap;
	va_start(ap, fmt);
	const int r = vsnprintf((char*)buf, blen, fmt, ap);
	va_end(ap);
	if (r < 0)
		return pl_error(p, PL_ERROR_OUTPUT_E);
	for (size_t i = 0; i < blen && (ch = buf[i]); i++)
		if (pl_put(p, ch) < 0)
			return pl_error(p, PL_ERROR_OUTPUT_E);
	return pl_error(p, 0);
}

static int pl_indent(prolog_t *p, size_t n) {
	assert(p);
	for (size_t i = 0; i < n; i++)
		if (pl_put(p, '\t') < 0)
			return pl_error(p, PL_ERROR_OUTPUT_E);
	return pl_error(p, 0);
}

static void *pl_alloc_cb(void *arena, void *ptr, size_t old_sz, size_t new_sz) {
	(void)arena;
	if (!new_sz) {
		free(ptr);
		return NULL;
	}
	if (old_sz > new_sz)
		return ptr;
	return realloc(ptr, new_sz);
}

static void pl_set_flag(unsigned *flags, const unsigned which, const int on) {
	assert(flags);
	if (on)
		*flags |= which;
	else
		*flags &= ~which;
}

static int pl_gc_off(prolog_t *p) {
	const int r = p->sysflags & PL_SFLAG_GC_OFF_E;
	pl_set_flag(&p->sysflags, PL_SFLAG_GC_OFF_E, 1);
	return r;
}

static int pl_gc_on(prolog_t *p) {
	const int r = p->sysflags & PL_SFLAG_GC_OFF_E;
	pl_set_flag(&p->sysflags, PL_SFLAG_GC_OFF_E, 0);
	return r;
}

static void pl_gc(prolog_t *p, int force);

static void *pl_allocate(prolog_t *p, const size_t bytes) { 
	assert(p); 
	assert(p->alloc);
	if (p->fatal)
		return NULL;
	void *r = p->alloc(p->arena, NULL, 0, bytes); 
	if (!r) { /* collect and then try again */
		pl_gc(p, 0);
		r = p->alloc(p->arena, NULL, 0, bytes);
		if (!r) {
			pl_error(p, PL_ERROR_OUT_OF_MEMORY_E);
			return NULL;
		}
	}
	p->gc_bytes_since_last_gc += bytes;
	memset(r, 0, bytes);
	return r;
}

static void *pl_reallocate(prolog_t *p, void *ptr, const size_t bytes) {
	assert(p);
	if (p->fatal)
		return NULL;
	void *r = p->alloc(p->arena, ptr, 0, bytes);
	if (!r) {
		p->fatal = PL_ERROR_OUT_OF_MEMORY_E;
		return NULL;
	}
	p->gc_bytes_since_last_gc += bytes;
	return r;
}

static void pl_release(prolog_t *p, void *ptr) {
	assert(p);
	assert(p->alloc);
	p->alloc(p->arena, ptr, 0, 0);
}

static char *pl_strdup(prolog_t *p, const char *s) {
	assert(p);
	assert(s);
	const size_t sz = strlen(s) + 1;
	char *r = pl_allocate(p, sz);
	return r ? memcpy(r, s, sz) : r;
}

static void pl_gc_stack_push(prolog_t *p, void *x, const int type) {
	assert(p);
	if (!p->stack) {
		const size_t sz = 512;
		p->stack = pl_allocate(p, sizeof (p->stack[0]) * sz);
		if (!p->stack)
			return;
		p->gc_stk_size = sz;
	}
	assert(p->gc_stk_idx < p->gc_stk_size);
	p->stack[p->gc_stk_idx].ptr = x;
	p->stack[p->gc_stk_idx].type = /*PL_MARK |*/ type;
	if ((p->gc_stk_idx + 1) >= p->gc_stk_size) {
		const size_t nsz = p->gc_stk_size * 2;
		assert(nsz > p->gc_stk_size);
		void *r = pl_reallocate(p, p->stack, sizeof (p->stack[0]) * nsz);
		if (!r)
			return;
		p->stack = r;
		p->gc_stk_size = nsz;
	}
	p->gc_stk_idx++;
}

static void *pl_gc_allocate(prolog_t *p, const size_t bytes, const int type) {
	assert(p);
	if (p->fatal)
		return NULL;
	if (!p->gc) {
		static const size_t gc_start_length = 512;
		p->gc = pl_allocate(p, sizeof (p->gc[0]) * gc_start_length);
		if (!p->gc)
			return NULL;
		p->gc_size = gc_start_length;
	}
	if (p->gc_bytes_since_last_gc >= PL_GC_THRESHOLD_BYTES) {
		p->gc_bytes_since_last_gc = 0;
		pl_gc(p, 0);
	}
	void *r = pl_allocate(p, bytes);
	if (!r) {
		return NULL;
	}
	assert(p->gc_used < p->gc_size);
	assert(type < 256);
	p->gc[p->gc_used].ptr = r;
	p->gc[p->gc_used].type = type;
	if ((p->gc_used + 1) >= p->gc_size) {
		const size_t new_size = p->gc_size * 2;
		assert(new_size > p->gc_size);
		void *n = pl_reallocate(p, p->gc, sizeof (p->gc[0]) * new_size);
		if (!n)
			return NULL;
		p->gc = n;
		p->gc_size = new_size;
	}
	p->gc_used++;
	pl_gc_stack_push(p, r, type);
	return r;
}

static void pl_gc_stack_set(prolog_t *p, size_t index) {
	assert(p);
	implies(p->gc_stk_size != 0, index < p->gc_stk_size);
	assert(index <= p->gc_stk_idx);
	p->gc_stk_idx = index;
}

static inline void pl_gc_set_or_clear_flag(pl_flags_t *flags, const int set) { assert(flags); if (set) { *flags |= PL_MARK; } else { *flags &= ~PL_MARK; } }

static void pl_gc_set(void *x, const int type, const int set) { /* "polymorphism" */
	if (!x) return;
	switch (type) {
	case PL_CONS: { pl_term_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_VAR: { pl_term_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_ATOM: { pl_atom_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_CLAUSE: { pl_clause_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_GOAL: { pl_goal_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_TRAIL: { pl_trail_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_PROGRAM: { pl_program_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	case PL_TVM: { pl_term_var_mapping_t *n = x; pl_gc_set_or_clear_flag(&n->flags, set); break; }
	default: never();
	}
}

static bool pl_gc_get(void *x, const int type) {
	if (!x) return true;
	pl_flags_t flags = 0;
	switch (type) {
	case PL_CONS: { pl_term_t *n = x; flags = n->flags; break; }
	case PL_VAR: { pl_term_t *n = x; flags = n->flags; break; }
	case PL_ATOM: { pl_atom_t *n = x; flags = n->flags; break; }
	case PL_CLAUSE: { pl_clause_t *n = x; flags = n->flags; break; }
	case PL_GOAL: { pl_goal_t *n = x; flags = n->flags; break; }
	case PL_TRAIL: { pl_trail_t *n = x; flags = n->flags; break; }
	case PL_PROGRAM: { pl_program_t *n = x; flags = n->flags; break; }
	case PL_TVM: { pl_term_var_mapping_t *n = x; flags = n->flags; break; }
	default: never();
	}
	return !!(flags & PL_MARK);
}

/* Notes; instead of using a flag bit to save on space you could instead just
 * use the Least Significant Bits to store the flag, as on all modern platforms
 * these bits should be zero when allocating a pointer due to alignment
 * restrictions, this is slightly not portable and "not allowed" by the C
 * standard, but doing things like this can greatly increase the efficiency
 * of the system. It is also not optimal storing the flags both in garbage
 * collection structure and also within the objects themselves. */
static void pl_gc_mark(prolog_t *p, void *x, const int type) {
	assert(p);
	nullable(x);
	if (!x)
		return;
	if (pl_gc_get(x, type))
		return;
	switch (type) {
	case PL_CONS: {
		pl_term_t *n = x;
		pl_gc_set(n, PL_CONS, 1);
		pl_gc_mark(p, n->t.cons.fsym, PL_ATOM);
		for (size_t i = 0; i < n->t.cons.arity; i++) {
			pl_term_t *t = n->t.cons.args[i];
			if (!t)
				continue;
			const int ntype = t->flags & PL_TYPE_MSK;
			pl_gc_mark(p, t, ntype);
		}
		break;
	}
	case PL_VAR: {
		pl_term_t *n = x;
		pl_gc_set(n, PL_VAR, 1);
		pl_term_t *t = n->t.var.instance;
		if (t) {
			const int ntype = t->flags & PL_TYPE_MSK;
			pl_gc_mark(p, t, ntype);
		}
		break;
	}
	case PL_ATOM: {
		pl_atom_t *n = x;
		pl_gc_set(n, PL_ATOM, 1);
		break;
	}
	case PL_CLAUSE: {
		pl_clause_t *n = x;
		pl_gc_set(n, PL_CLAUSE, 1);
		if (n->car) { 
			pl_term_t *t = n->car;
			const int ntype = t->flags & PL_TYPE_MSK;
			pl_gc_mark(p, t, ntype);
		}
		pl_gc_mark(p, n->cdr, PL_GOAL);
		break;
	}
	case PL_GOAL: {
		pl_goal_t *n = x;
		pl_gc_set(n, PL_GOAL, 1);
		if (n->car) {
			pl_term_t *t = n->car;
			const int ntype = t->flags & PL_TYPE_MSK;
			pl_gc_mark(p, t, ntype);
		}
		pl_gc_mark(p, n->cdr, PL_GOAL);
		break;
	}
	case PL_TRAIL: {
		pl_trail_t *n = x;
		pl_gc_set(n, PL_TRAIL, 1);
		if (n->car) {
			pl_term_t *t = n->car;
			const int ntype = t->flags & PL_TYPE_MSK;
			pl_gc_mark(p, t, ntype);
		}
		pl_gc_mark(p, n->cdr, PL_TRAIL);
		break;
	}
	case PL_PROGRAM: {
		pl_program_t *n = x;
		pl_gc_set(n, PL_PROGRAM, 1);
		pl_gc_mark(p, n->car, PL_CLAUSE);
		pl_gc_mark(p, n->cdr, PL_PROGRAM);
		break;
	}
	case PL_TVM: {
		pl_term_var_mapping_t *n = x;
		pl_gc_set(n, PL_TVM, 1);
		if (n->var) {
			for (size_t i = 0; i < n->length; i++) {
				pl_term_t *t = n->var[i];
				if (!t)
					continue;
				const int ntype = t->flags & PL_TYPE_MSK;
				assert(ntype == PL_VAR);
				pl_gc_mark(p, t, ntype);
			}
		}
		break;
	}
	default: never();
	}
}

static void pl_gc_free(prolog_t *p, void *x, const int type) {
	assert(p);
	nullable(x);
	if (!x)
		return;
	switch (type) {
	case PL_CONS: {
		pl_term_t *n = x;
		pl_release(p, n->t.cons.args);
		n->t.cons = (pl_term_cons_t) { 0, };
		pl_release(p, n);
		break;
	}
	case PL_VAR: {
		pl_term_t *n = x;
		n->t.var.instance = NULL;
		pl_release(p, n);
		break;
	}
	case PL_ATOM: {
		pl_atom_t *n = x;
		pl_release(p, n->name);
		n->name = NULL;
		pl_release(p, n);
		break;
	}
	case PL_CLAUSE: {
		pl_clause_t *n = x;
		*n = (pl_clause_t) { 0, };
		pl_release(p, n);
		break;
	}
	case PL_GOAL: {
		pl_goal_t *n = x;
		*n = (pl_goal_t) { 0, };
		pl_release(p, n);
		break;
	}
	case PL_TRAIL: {
		pl_trail_t *n = x;
		*n = (pl_trail_t) { 0, };
		pl_release(p, n);
		break;
	}
	case PL_PROGRAM: {
		pl_program_t *n = x;
		*n = (pl_program_t) { 0, };
		pl_release(p, n);
		break;
	}
	case PL_TVM: {
		pl_term_var_mapping_t *n = x;
		for (size_t i = 0; i < n->length; i++) {
			if (n->name) {
				pl_release(p, n->name[i]);
				n->name[i] = NULL;
			}
			if (n->var)
				n->var[i] = NULL;
		}
		pl_release(p, n->var);
		pl_release(p, n->name);
		n->var = NULL;
		n->name = NULL;
		pl_release(p, n);
		break;
	}
	default: never();
	}
}

static void pl_sweep(prolog_t *p) {
	assert(p);
	size_t left = p->gc_used;
	for (size_t i = 0; i < p->gc_used; i++) {
		void *ptr = p->gc[i].ptr;
		const int type = p->gc[i].type & PL_TYPE_MSK;
		if (pl_gc_get(ptr, type)) {
			pl_gc_set(ptr, type, 0);
			continue;
		}
		pl_gc_free(p, p->gc[i].ptr, type);
		p->gc[i].ptr = NULL;
		left--;
	}
	for (size_t i = 0; i < p->gc_used && i < left; i++) { /* compact */
		if (p->gc[i].ptr == NULL) {
			size_t j = i;
			for (;j < p->gc_used && p->gc[j].ptr == NULL; j++)
				/*do nothing*/;
			if (j >= p->gc_used)
				break;
			p->gc[i] = p->gc[j];
			p->gc[j].ptr = NULL;
			i = j;
		}
	}
	// TODO: Fix this!
	/*p->gc_used = left;*/
}

static void pl_gc(prolog_t *p, const int force) {
	assert(p);
	const int on = force || !(p->sysflags & PL_SFLAG_GC_OFF_E);
	if (!on)
		return;
	pl_gc_mark(p, p->db, PL_PROGRAM);
	pl_gc_mark(p, p->goal, PL_GOAL);
	pl_gc_mark(p, p->sofar, PL_TRAIL);
	pl_gc_mark(p, p->goal, PL_GOAL);
	pl_gc_mark(p, p->map, PL_TVM);
	for (size_t i = 0; i < p->gc_stk_idx; i++)
		pl_gc_mark(p, p->stack[i].ptr, p->stack[i].type & PL_TYPE_MSK);
	pl_sweep(p);
	p->gc_bytes_since_last_gc = 0;
}

static pl_atom_t *pl_atom_new(prolog_t *p, const char *name) {
	assert(p);
	assert(name);
	pl_atom_t *r = pl_gc_allocate(p, sizeof (*r), PL_ATOM);
	if (!r)
		return NULL;
	r->flags = PL_MARK | PL_ATOM;
	r->name = pl_strdup(p, name);
	if (!(r->name))
		return NULL;
	return r;
}

static int pl_atom_print(prolog_t *p, pl_atom_t *a) {
	assert(p);
	assert(a);
	assert(a->name);
	if (p->fatal)
		return pl_error(p, -1);
	const int r = pl_puts(p, a->name) < 0 ? -1 : 0;
	return pl_error(p, r);
}

static int pl_atom_equal(pl_atom_t *a, pl_atom_t *b) {
	assert(a);
	assert(b);
	assert(a->name);
	assert(b->name);
	return !strcmp(a->name, b->name);
}

static pl_term_t *pl_term_cons_new(prolog_t *p, pl_atom_t *fsym, size_t arity, pl_term_t **terms) {
	assert(p);
	assert(fsym);
	mutual(arity != 0, terms);
	pl_term_t *c = pl_gc_allocate(p, sizeof(*c), PL_CONS);
	if (!c)
		return NULL;
	c->flags = PL_MARK | PL_CONS;
	c->t.cons.arity = arity;
	c->t.cons.fsym = fsym;
	c->t.cons.args = NULL;
	if (arity) {
		c->t.cons.args = pl_allocate(p, sizeof(c->t.cons.args[0]) * arity);
		if (!c->t.cons.args)
			return NULL;
		for (size_t i = 0; i < arity; i++)
			c->t.cons.args[i] = terms[i];
	}
	return c;
}

static pl_term_t *pl_term_var_new(prolog_t *p) {
	assert(p);
	pl_term_t *r = pl_gc_allocate(p, sizeof(*r), PL_VAR);
	if (!r)
		return NULL;
	r->flags = PL_MARK | PL_VAR;
	r->t.var.varno = ++(p->varno);
	r->t.var.instance = r;
	return r;
}

static void pl_trail_push(prolog_t *p, pl_term_t *x);

static pl_term_t *pl_term_copy(prolog_t *p, pl_term_t *t) {
	assert(p);
	assert(t);
	if (p->fatal)
		return NULL;
	switch (t->flags & PL_TYPE_MSK) {
	case PL_CONS: {
		pl_term_t *c = pl_gc_allocate(p, sizeof *c, PL_CONS);
		if (!c)
			return NULL;
		c->flags = PL_MARK | PL_CONS;
		c->t.cons.arity = t->t.cons.arity;
		c->t.cons.fsym = pl_atom_new(p, t->t.cons.fsym->name);
		if (!c->t.cons.fsym)
			return NULL;
		c->t.cons.args = NULL;
		if (t->t.cons.arity) {
			c->t.cons.args = pl_allocate(p, sizeof (t->t.cons.args[0]) * t->t.cons.arity);
			if (!c->t.cons.args)
				return NULL;
			for (size_t i = 0; i < t->t.cons.arity; i++)
				c->t.cons.args[i] = pl_term_copy(p, t->t.cons.args[i]);
		}
		return c;
	}
	case PL_VAR: {
		if (t->t.var.instance == t) {
			pl_trail_push(p, t);
			pl_term_t *v = pl_term_var_new(p);
			t->t.var.instance = v;
			return v;
		}
		return t->t.var.instance;
	}
	default:
		never();
	}
	return NULL;
}

static int pl_term_print(prolog_t *p, pl_term_t *t) {
	assert(p);
	assert(t);
	switch (t->flags & PL_TYPE_MSK) {
	case PL_CONS: {
		if (pl_atom_print(p, t->t.cons.fsym) < 0) return pl_error(p, -1);
		if (t->t.cons.arity > 0) {
			if (pl_puts(p, "(") < 0) return pl_error(p, -1);
			for (size_t i = 0; i < t->t.cons.arity; i++) {
				if (pl_term_print(p, t->t.cons.args[i]) < 0) return pl_error(p, -1);
				if (i < (t->t.cons.arity - 1))
					if (pl_puts(p, ",") < 0) return pl_error(p, -1);
			}
			if (pl_puts(p, ")") < 0) return pl_error(p, -1);
		}
		break;
	}
	case PL_VAR:
		// TODO: Print out variable name if known, this should help in
		// debugging the interpreter.
		if (t->t.var.instance != t) {
			if (pl_term_print(p, t->t.var.instance) < 0) return pl_error(p, -1);
		} else {
			if (pl_putf(p, p->buf, sizeof p->buf, "_%d", t->t.var.varno) < 0) return pl_error(p, -1);
		}
		break;
	default: never();
	}
	return pl_error(p, 0);
}

static bool pl_term_unify(prolog_t *p, pl_term_t *s, pl_term_t *t) {
	assert(p);
	assert(s);
	assert(t);
	switch (s->flags & PL_TYPE_MSK) {
	case PL_CONS: {
		if ((t->flags & PL_TYPE_MSK) != PL_CONS) {
			assert((t->flags & PL_TYPE_MSK) == PL_VAR);
			return pl_term_unify(p, t, s);
		}
		pl_term_t *x = t; /* swap unification target */
		t = s;
		s = x;
		if (!pl_atom_equal(s->t.cons.fsym, t->t.cons.fsym) || s->t.cons.arity != t->t.cons.arity)
			return false;
		for (size_t i = 0; i < s->t.cons.arity; i++)
			if (!pl_term_unify(p, s->t.cons.args[i], t->t.cons.args[i]))
				return false;
		return true;
	}
	case PL_VAR: {
		if (s->t.var.instance != s)
			return pl_term_unify(p, s->t.var.instance, t);
		pl_trail_push(p, s);
		s->t.var.instance = t;
		return true;
	}
	default: 
		never();
	}
	return false;
}

static pl_clause_t *pl_clause_new(prolog_t *p, pl_term_t *car, pl_goal_t *cdr) {
	assert(p);
	assert(car);
	assert((car->flags & PL_TYPE_MSK) == PL_CONS);
	pl_clause_t *c = pl_gc_allocate(p, sizeof *c, PL_CLAUSE);
	if (!c)
		return NULL;
	c->flags = PL_MARK | PL_CLAUSE;
	c->car = car;
	c->cdr = cdr;
	return c;
}

static pl_goal_t *pl_goal_new(prolog_t *p, pl_term_t *car, pl_goal_t *cdr) {
	assert(p);
	assert(car);
	// TODO: This is this way because of the way the parse is, really it
	// should only allow PL_CONS but it was reused as a list, the grammar
	// should really be changed.
	//assert((car->flags & PL_TYPE_MSK) == PL_CONS);
	pl_goal_t *g = pl_gc_allocate(p, sizeof *g, PL_GOAL);
	if (!g)
		return NULL;
	g->flags = PL_MARK | PL_GOAL;
	g->car = car;
	g->cdr = cdr;
	return g;
}

static pl_trail_t *pl_trail_new(prolog_t *p, pl_term_t *tvar, pl_trail_t *cdr) {
	assert(p);
	assert(tvar);
	assert((tvar->flags & PL_TYPE_MSK) == PL_VAR);
	pl_trail_t *t = pl_gc_allocate(p, sizeof *t, PL_TRAIL);
	if (!t)
		return NULL;
	t->flags = PL_MARK | PL_TRAIL;
	t->car = tvar;
	t->cdr = cdr;
	return t;
}

static pl_trail_t *pl_trail_note(prolog_t *p) {
	assert(p);
	return p->sofar;
}

static void pl_trail_push(prolog_t *p, pl_term_t *x) {
	assert(p);
	assert(x);
	assert((x->flags & PL_TYPE_MSK) == PL_VAR);
	pl_trail_t *n = pl_trail_new(p, x, p->sofar);
	if (!n)
		return;
	p->sofar = n;
}

static void pl_term_var_reset(pl_term_t *t) {
	assert(t);
	assert((t->flags & PL_TYPE_MSK) == PL_VAR);
	t->t.var.instance = t;
}

static void pl_trail_undo(prolog_t *p, pl_trail_t *whereto) {
	assert(p);
	/*assert(whereto);*/
	for (; p->sofar != whereto; p->sofar = p->sofar->cdr)
		pl_term_var_reset(p->sofar->car);
}

static pl_program_t *pl_program_new(prolog_t *p, pl_clause_t *car, pl_program_t *cdr) {
	assert(p);
	assert(car);
	pl_program_t *c = pl_gc_allocate(p, sizeof *c, PL_PROGRAM);
	if (!c)
		return NULL;
	c->flags = PL_MARK | PL_PROGRAM;
	c->car = car;
	c->cdr = cdr;
	return c;
}

static pl_goal_t *pl_goal_copy(prolog_t *p, pl_goal_t *g) {
	assert(p);
	assert(g);
	pl_term_t *x = pl_term_copy(p, g->car);
	pl_goal_t *n = g->cdr ? pl_goal_copy(p, g->cdr) : NULL;
	return pl_goal_new(p, x, n);
}


static pl_goal_t *pl_goal_append(prolog_t *p, pl_goal_t *g, pl_goal_t *l) {
	assert(p);
	assert(g);
	return pl_goal_new(p, g->car, g->cdr ? pl_goal_append(p, g->cdr, l) : l /* NULL? */);
}

static int pl_goal_print(prolog_t *p, pl_goal_t *g) {
	assert(p);
	assert(g);
	if (pl_term_print(p, g->car) < 0) return pl_error(p, -1);
	if (g->cdr) {
		if (pl_puts(p, "; ") < 0) return pl_error(p, -1);
		return pl_goal_print(p, g->cdr);
	}
	return pl_error(p, 0);
}

static pl_clause_t *pl_clause_copy(prolog_t *p, pl_clause_t *c) {
	assert(p);
	assert(c);
	pl_term_t *x = pl_term_copy(p, c->car);
	pl_goal_t *g = c->cdr ? pl_goal_copy(p, c->cdr) : NULL;
	return pl_clause_new(p, x, g);
}

static int pl_clause_print(prolog_t *p, pl_clause_t *c) {
	assert(p);
	assert(c);
	if (pl_term_print(p, c->car) < 0) return pl_error(p, -1);
	if (pl_puts(p, " :- ") < 0) return pl_error(p, -1);
	if (!c->cdr)
		return pl_puts(p, "true") < 0 ? -1 : 0;
	return pl_goal_print(p, c->cdr);
}

static int pl_term_var_mapping_show_answer(prolog_t *p, pl_term_var_mapping_t *map) {
	assert(p);
	if (!map || map->length == 0 || (p->sysflags & PL_SFLAG_ONLY_PRINT_YES_ON_MATCH))
		return pl_puts(p, "yes\n") < 0 ? -1 : 0;
	for (size_t i = 0; i < map->length; i++) {
		if (pl_putf(p, p->buf, sizeof p->buf, "%s = ", map->name[i]) < 0) return pl_error(p, -1);
		if (pl_term_print(p, map->var[i]) < 0) return pl_error(p, -1);
		if (pl_puts(p, "\n") < 0) return pl_error(p, -1);
	}
	return pl_error(p, 0);
}

static int pl_goal_solver_step(prolog_t *p, pl_goal_t *g, pl_program_t *prog, int level, pl_term_var_mapping_t *map) {
	assert(p);
	assert(g);
	assert(prog);
	if (p->fatal)
		return pl_error(p, -1);
	//if (level == 0) 
	//	pl_gc_stack_set(p, 0);
	if (p->maxlevel) {
		if (level > p->maxlevel) {
			(void)pl_putf(p, p->buf, sizeof p->buf, "maxlevel exceeded: %d\n", level);
			return -1; /* return non fatal error */
		}
	}
	/* assert(map); <- nullable */
	if (!(p->sysflags & PL_SFLAG_PRINT_ONLY_MATCHES)) {
		if (pl_indent(p, level) < 0) return pl_error(p, -1);
		if (pl_putf(p, p->buf, sizeof p->buf, "solve@%d: ", level) < 0) return pl_error(p, -1);
		if (pl_goal_print(p, g) < 0) return pl_error(p, -1);
		if (pl_puts(p, "\n") < 0) return pl_error(p, -1);
	}
	const size_t gstk = p->gc_stk_idx;
	for (pl_program_t *q = prog; q != NULL; q = q->cdr) {
		pl_trail_t *t = pl_trail_note(p);
		//pl_gc_stack_push(p, t, PL_TRAIL);
		pl_clause_t *c = pl_clause_copy(p, q->car); // TODO: add to gc stack
		//pl_gc_stack_push(p, c, PL_CLAUSE);
		pl_trail_undo(p, t);
		if (!(p->sysflags & PL_SFLAG_PRINT_ONLY_MATCHES)) {
			if (pl_indent(p, level) < 0) return pl_error(p, -1);
			if (pl_puts(p, "  try:") < 0) return pl_error(p, -1);
			if (pl_clause_print(p, c) < 0) return pl_error(p, -1);
			if (pl_puts(p, "\n") < 0) return pl_error(p, -1);
		}
		if (pl_term_unify(p, g->car, c->car)) {
			pl_goal_t *gdash = c->cdr == NULL ? g->cdr : pl_goal_append(p, c->cdr, g->cdr);
			//pl_gc_stack_push(p, gdash, PL_GOAL);
			if (gdash == NULL) {
				if (pl_term_var_mapping_show_answer(p, map) < 0)
					return pl_error(p, -1);
			} else {
				if (pl_goal_solver_step(p, gdash, prog, level + 1, map) < 0)
					return -1; /* potential non fatal error */
			}
		} else {
			if (!(p->sysflags & PL_SFLAG_PRINT_ONLY_MATCHES)) {
				if (pl_indent(p, level) < 0) return pl_error(p, -1);
				if (pl_puts(p, "  nomatch.\n") < 0) return pl_error(p, -1);
			}
		}
		pl_trail_undo(p, t);
		if (p->fatal)
			return pl_error(p, -1);
	}
	pl_gc_stack_set(p, gstk);
	return pl_error(p, 0);
}

static pl_term_var_mapping_t *pl_term_var_mapping_new(prolog_t *p, pl_term_t **ts, char **names, size_t count) {
	assert(p);
	mutual(count != 0, ts);
	mutual(count != 0, names);
	pl_term_var_mapping_t *tvm = pl_gc_allocate(p, sizeof *tvm, PL_TVM);
	// TODO: Rename vars
	pl_term_t **_ts = count ? pl_allocate(p, sizeof (_ts[0]) * count) : NULL;
	char **_names = count ? pl_allocate(p, sizeof (_names[0]) * count) : NULL;
	if (count) {
		if (!tvm || !_ts || !_names) {
			pl_release(p, tvm);
			pl_release(p, _ts);
			pl_release(p, _names);
			return NULL;
		}
	} else {
		if (!tvm)
			return NULL;
	}
	tvm->flags = PL_MARK | PL_TVM;
	tvm->var = _ts;
	tvm->name = _names;
	tvm->length = count;
	for (size_t i = 0; i < count; i++) {
		_ts[i] = ts[i];
		char *name = pl_strdup(p, names[i]);
		_names[i] = name;
		if (!name) /* gc will handle this */
			return NULL;
	}
	return tvm;
}

static pl_term_t *pl_term_var_mapping_search(pl_term_var_mapping_t *map, const char *name) {
	assert(map);
	assert(name);
	for (pl_term_var_mapping_t *m = map; m; m = m->parent)
		for (size_t i = 0; i < m->length; i++)
			if (!strcmp(m->name[i], name))
				return m->var[i];
	return NULL;
}

static pl_term_t *pl_term_var_mapping_add(prolog_t *p, pl_term_var_mapping_t *map, const char *name) {
	assert(p);
	assert(map);
	assert(name);
	pl_term_t *t = pl_term_var_mapping_search(map, name);
	if (t)
		return t;
	char **_name = NULL;
	pl_term_t **ts = pl_reallocate(p, map->var, sizeof (ts[0]) * (map->length + 1));
	if (!ts)
		return NULL;
	map->var = ts;
	_name = pl_reallocate(p, map->name, sizeof (_name[0]) * (map->length + 1));
	if (!_name) /* partial initialization handled by GC */
		return NULL;
	map->name = _name;
	char *n = pl_strdup(p, name);
	if (!n) /* partial initialization handled by GC */
		return NULL;
	map->name[map->length] = n;
	t = pl_term_var_new(p);
	map->var[map->length] = t;
	map->length++;
	return t;
}

static inline pl_term_t *pl_cons0(prolog_t *p, pl_atom_t *a) { return pl_term_cons_new(p, a, 0, NULL); }
static inline pl_term_t *pl_cons1(prolog_t *p, pl_atom_t *a, pl_term_t *x) { return pl_term_cons_new(p, a, 1, (pl_term_t *[]) {x}); }
static inline pl_term_t *pl_cons2(prolog_t *p, pl_atom_t *a, pl_term_t *x, pl_term_t *y) { return pl_term_cons_new(p, a, 2, (pl_term_t *[]){x, y}); }
static inline pl_term_t *pl_cons3(prolog_t *p, pl_atom_t *a, pl_term_t *x, pl_term_t *y, pl_term_t *z) { return pl_term_cons_new(p, a, 3, (pl_term_t *[]){x, y, z}); }

static int pl_put_file_cb(void *out, const int ch) { assert(out); return fputc(ch, out) < 0 ? -1 : 0; }
static int pl_get_file_cb(void *in) { assert(in); return fgetc(in); }

typedef struct { const char *program; size_t length; size_t _index; } pl_get_string_t;

static int pl_get_string_cb(void *in) {
	assert(in);
	pl_get_string_t *s = in;
	if (!s->length)
		return -1;
	assert(s->program);
	assert(s->_index <= s->length);
	if (s->_index < s->length)
		return s->program[s->_index++];
	return -1;
}

/* avoid locale.h see <https://github.com/mpv-player/mpv/commit/1e70e82baa9193f6f027338b0fab0f5078971fbe> */
static int pl_isupper(const int ch) { return ch >= 'A' && ch <= 'Z'; }
static int pl_islower(const int ch) { return ch >= 'a' && ch <= 'z'; }
static int pl_isalpha(const int ch) { return pl_islower(ch) || pl_isupper(ch); }

static int pl_lexer(prolog_t *p) {
	pl_lexer_t *l = &p->lex;
	int ch = 0;
again:
	ch = pl_get(p);
	switch (ch) {
	case 0: case ' ': case '\t': case '\n': case '\r': goto again;
	case '%': {
		for (; (ch = pl_get(p)) != '\n';)
			if (ch == -1) 
				return PLEX_EOF;
		if (pl_ungetc(p, ch) < 0) return PLEX_ERROR;
		goto again;
	}
	case ',': return PLEX_COMMA;
	case '.': return PLEX_DOT;
	case '(': return PLEX_LPAR;
	case '?': 
		ch = pl_get(p);
		if (ch != '-')
			return PLEX_ERROR;
		return PLEX_QUERY;
	case ')': return PLEX_RPAR;
	case ':': {
		ch = pl_get(p);
		if (ch != '-')
			return PLEX_ERROR;
		return PLEX_IS;
	}
	case -1: return PLEX_EOF;
	default: {
		if (!pl_isalpha(ch))
			return PLEX_ERROR;
		l->used = 0;
		if (l->length == 0) {
			const size_t length = 256;
			l->buf = pl_allocate(p, length);
			if (!l->buf)
				return PLEX_ERROR;
			l->length = length;
		}
		do {
			assert(l->used < l->length);
			l->buf[l->used++] = ch;
			if (l->used >= (l->length - 1)) {
				const size_t nlength = l->length * 2l;
				assert(nlength > l->length);
				uint8_t *n = pl_reallocate(p, l->buf, nlength);
				if (!n)
					return PLEX_ERROR;
				l->buf = n;
				l->length = nlength;
			}
			ch = pl_get(p);
			if (!pl_isalpha(ch)) {
				if (pl_ungetc(p, ch) < 0)
					return PLEX_ERROR;
				break;
			}
		} while (true);
		l->buf[l->used] = 0;
		if (pl_isupper(l->buf[0]))
			return PLEX_VAR;
		return PLEX_ATOM;
	}
	}
	return PLEX_ERROR;
}

static int pl_accept(prolog_t *p, int sym) {
	assert(p);
	if (p->sym == sym) {
		if (p->sysflags & PL_SFLAG_PARSER_DEBUG) {
			uint8_t buf[32] = { 0, };
			(void)pl_putf(p, buf, sizeof (buf), "%c%c", sym, sym == PLEX_DOT || sym == PLEX_EOF ? '\n' : ' ');
		}
		p->sym = pl_lexer(p);
		return 1;
	}
	return 0;
}

static int pl_expect(prolog_t *p, int sym) {
	assert(p);
	if (pl_accept(p, sym))
		return 1;
	uint8_t buf[128] = { 0, };
	if (pl_putf(p, buf, sizeof buf, "error: invalid parse, expected: %d/'%c'\n", sym, sym) < 0)
		return -1;
	return 0;
}

static pl_term_t *pl_term_append(prolog_t *p, pl_term_t *t, pl_term_t *append) {
	assert(p);
	assert(t);
	assert(append);
	pl_term_t **nargs = pl_reallocate(p, t->t.cons.args, (t->t.cons.arity + 1) * sizeof (nargs[0]));
	if (!nargs)
		return NULL;
	t->t.cons.args = nargs;
	t->t.cons.args[t->t.cons.arity++] = append;
	return t;
}

static int pl_grm_id(prolog_t *p, pl_atom_t **atom) {
	assert(p);
	assert(atom);
	if (pl_expect(p, PLEX_ATOM)) {
		*atom = pl_atom_new(p, (char*)p->lex.buf);
		return 1;
	}
	return 0;
}

static int pl_grm_rule(prolog_t *p, pl_term_var_mapping_t *map, pl_goal_t **goal, int var);

static int pl_grm_term(prolog_t *p, pl_term_var_mapping_t *map, pl_term_t **term, int var) {
	assert(p);
	assert(term);

	/* // Test code, this does not work because elsewhere cons/var are treated differently
	pl_atom_t *atom = NULL;
	pl_term_t *nterm = NULL;
	if (pl_accept(p, PLEX_VAR)) {
		pl_term_t *t = pl_term_var_mapping_search(map, (char*)p->lex.buf);
		if (!t)
			t = pl_term_var_mapping_add(p, map, (char*)p->lex.buf);
		nterm = t;
		*term = t;
		return 1;
	} else if (pl_expect(p, PLEX_ATOM)) {
		atom = pl_atom_new(p, (char*)p->lex.buf);
		nterm = pl_term_cons_new(p, atom, 0, NULL);
	} else {
		return 0;
	}
	*term = nterm;
	*/

	if (var) {
		if (pl_accept(p, PLEX_VAR)) {
			pl_term_t *t = pl_term_var_mapping_search(map, (char*)p->lex.buf);
			if (!t)
				t = pl_term_var_mapping_add(p, map, (char*)p->lex.buf);
			*term = t;
			return 1;
		}
	}

	pl_atom_t *atom = NULL;
	if (!pl_grm_id(p, &atom))
		return 0;
	pl_term_t *nterm = pl_term_cons_new(p, atom, 0, NULL);
	*term = nterm;
	if (pl_accept(p, PLEX_LPAR)) {
		pl_goal_t *goal = NULL;
		if (!pl_grm_rule(p, map, &goal, 1))
			return 0;
		for (pl_goal_t *n = goal; n; n = n->cdr)
			if (!pl_term_append(p, nterm, n->car))
				break;
		return pl_expect(p, PLEX_RPAR);
	}
	return 1;
}

static int pl_grm_rule(prolog_t *p, pl_term_var_mapping_t *map, pl_goal_t **goal, int var) {
	assert(p);
	assert(goal);
	pl_goal_t *g = NULL, *h = NULL;
	do {
		pl_term_t *nterm = NULL;
		if (!pl_grm_term(p, map, &nterm, var))
			return 0;
		if (!g) {
			g = pl_goal_new(p, nterm, NULL);
			h = g;
		} else {
			g->cdr = pl_goal_new(p, nterm, NULL);
			if (!g->cdr)
				return 0;
			g = g->cdr;
		}
	} while (pl_accept(p, PLEX_COMMA));
	*goal = h;
	return 1;
}

static int pl_grm_goal(prolog_t *p, pl_term_var_mapping_t *map, pl_goal_t **goal) {
	assert(p);
	assert(goal);
	if (!pl_grm_rule(p, map, goal, 0))
		return 0;
	return 1;
}

static int pl_grm_clause(prolog_t *p, pl_term_var_mapping_t *map, pl_clause_t **clause) {
	assert(p);
	assert(clause);
	pl_term_t *term = NULL;
	pl_goal_t *goal = NULL;
	if (!pl_grm_term(p, map, &term, 0))
		return 0;
	if (pl_accept(p, PLEX_IS))
		if (!pl_grm_rule(p, map, &goal, 0))
			return 0;
	*clause = pl_clause_new(p, term, goal);
	return 1;
}

static int pl_grm_program(prolog_t *p, pl_term_var_mapping_t *map, pl_program_t **program, pl_goal_t **goal) {
	assert(p);
	assert(program);
	p->sym = pl_lexer(p);
	pl_program_t *progs = NULL, *head = NULL;
	do {
		if (pl_accept(p, PLEX_EOF)) {
			*program = head;
			return 1;
		}
		if (pl_accept(p, PLEX_DOT))
			continue;
		if (pl_accept(p, PLEX_QUERY)) {
			pl_goal_t *ngoal = NULL;
			if (!pl_grm_goal(p, map, &ngoal))
				return 0;
			if (!pl_expect(p, PLEX_DOT))
				return 0;
			/* return after 1 goal for now */
			*program = head;
			*goal = ngoal;
			return 1;
		} else {
			pl_clause_t *clause = NULL;
			pl_term_var_mapping_t *nmap = pl_term_var_mapping_new(p, NULL, NULL, 0);
			if (!pl_grm_clause(p, nmap, &clause))
				return 0;
			if (p->sysflags & PL_SFLAG_REVERSE_PROGRAM_ORDER) {
				progs = pl_program_new(p, clause, progs);
				head = progs;
			} else {
				pl_program_t *np = pl_program_new(p, clause, NULL);
				if (!head) {
					head = np;
					progs = np;
				} else {
					assert(progs);
					progs->cdr = np;
					progs = np;
				}
			}
		}
	} while (pl_accept(p, PLEX_DOT));
	*program = head;
	return pl_expect(p, PLEX_EOF);
}

static int pl_parse(prolog_t *p, pl_term_var_mapping_t *map, pl_program_t **program, pl_goal_t **goal) {
	assert(p);
	return pl_grm_program(p, map, program, goal);
}

static pl_program_t *pl_program_tail(pl_program_t *prog) {
	assert(prog);
	pl_program_t *q = prog;
	for (;q && q->cdr; q = q->cdr)
		;
	implies(prog, q);
	return q;
}

static int pl_program_append(prolog_t *p, pl_program_t *prog) {
	assert(p);
	if (!prog)
		return 0;
	if (!p->db) {
		p->db = prog;
		p->tail = pl_program_tail(p->db);
		return 0;
	} 
	const int reverse = !!(p->sysflags & PL_SFLAG_REVERSE_PROGRAM_ORDER);
	if (reverse) {
		p->tail = pl_program_tail(prog);
		p->tail->cdr = p->db;
		p->db = prog;
	} else {
		assert(p->tail);
		p->tail->cdr = prog;
		p->tail = pl_program_tail(prog);
	}
	return 0;
}

static int pl_goal_solve(prolog_t *p, pl_goal_t *g, pl_program_t *prog, pl_term_var_mapping_t *map) {
	assert(p);
	if (pl_program_append(p, prog) < 0)
		return pl_error(p, -1);
	if (!g)
		return 0;
	if (!prog && !p->db) {
		if (pl_puts(p, "No program.\n") < 0)
			return pl_error(p, PL_ERROR_OUTPUT_E);
		return 0;
	}
	p->goal = g;
	p->map = map;
	const size_t prior = p->gc_stk_idx;
	const int r = pl_goal_solver_step(p, g, p->db, 0, map);
	pl_gc_stack_set(p, prior);
	return r;
}

static int pl_eval(prolog_t *p, int (*get)(void *in), void *in) {
	assert(p);
	int r = 0;
	int (*tget)(void *in) = p->get;
	void *tin = p->in;
	pl_term_var_mapping_t *map = pl_term_var_mapping_new(p, NULL, NULL, 0);
	pl_program_t *program = NULL;
	pl_goal_t *goal = NULL;
	p->get = get;
	p->in = in;
	p->varno = 1;
	p->sym = 0;
	while (p->sym != PLEX_EOF && p->sym != PLEX_ERROR && !p->fatal) {
		if (p->prompt) {
			if (pl_puts(p, p->prompt) < 0) {
				r = -1;
				goto end;
			}
		}
		const int st = pl_parse(p, map, &program, &goal);
		if (!st) {
			r = -1;
			goto end;
		}
		if (pl_goal_solve(p, goal, program, map) < 0) {
			r = -1;
			goto end;
		}
	}
end:
	p->in = tin;
	p->get = tget;
	return r;
}


static int pl_eval_string(prolog_t *p, const char *s) {
	assert(s);
	pl_get_string_t v = { .program = s, .length = strlen(s), };
	return pl_eval(p, pl_get_string_cb, &v);
}


static int pl_eval_file(prolog_t *p, FILE *f) {
	assert(f);
	return pl_eval(p, pl_get_file_cb, f);
}

static void pl_reset(prolog_t *p) {
	assert(p);
	p->db = NULL;
	p->tail = NULL;
}

/* Instead of parsing a string we can instead construct a prolog program via
 * calling prolog constructs directly. It is far more cumbersome, but it has
 * some utility (especially if you can generate this code). */
static int pl_test1(prolog_t *p) {
	assert(p);
	pl_atom_t *at_app = pl_atom_new(p, "app");
	pl_atom_t *at_cons = pl_atom_new(p, "cons");
	pl_term_t *f_nil = pl_cons0(p, pl_atom_new(p, "nil"));
	pl_term_t *f_1 = pl_cons0(p, pl_atom_new(p, "1"));
	pl_term_t *f_2 = pl_cons0(p, pl_atom_new(p, "2"));
	pl_term_t *f_3 = pl_cons0(p, pl_atom_new(p, "3"));

	pl_term_t *v_x = pl_term_var_new(p);
	pl_term_t *lhs1 = pl_cons3(p, at_app, f_nil, v_x, v_x);
	pl_clause_t *c1 = pl_clause_new(p, lhs1, NULL);

	pl_term_t *v_l = pl_term_var_new(p);
	pl_term_t *v_m = pl_term_var_new(p);
	pl_term_t *v_n = pl_term_var_new(p);
	pl_term_t *rhs2 = pl_cons3(p, at_app, v_l, v_m, v_n);
	pl_term_t *lhs2a = pl_cons2(p, at_cons, v_x, v_l);
	pl_term_t *lhs2b = pl_cons2(p, at_cons, v_x, v_n);
	pl_term_t *lhs2 = pl_cons3(p, at_app, lhs2a, v_m, lhs2b);
	pl_clause_t *c2 = pl_clause_new(p, lhs2, pl_goal_new(p, rhs2, NULL));

	pl_term_t *v_i = pl_term_var_new(p);
	pl_term_t *v_j = pl_term_var_new(p);
	pl_term_t *rhs3 = pl_cons3(p, at_app, v_i, v_j, 
			pl_cons2(p, at_cons, f_1, pl_cons2(p, at_cons, f_2, pl_cons2(p, at_cons, f_3, f_nil))));

	pl_goal_t *g1 = pl_goal_new(p, rhs3, NULL);

	pl_program_t *test_p1 = pl_program_new(p, c1, pl_program_new(p, c2, NULL));
	pl_program_t *test_p2 = pl_program_new(p, c2, pl_program_new(p, c1, NULL));

	pl_term_t *varvar[] = { v_i, v_j, };
	char *varname[] =  { "I", "J", };
	pl_term_var_mapping_t *var_name_map = pl_term_var_mapping_new(p, varvar, varname, NELEMS(varname));

	if (pl_puts(p, "=======Append with traditional clause order:\n") < 0) return -1;
	pl_goal_solve(p, g1, test_p1, var_name_map);
	pl_reset(p);
	if (pl_puts(p, "\n=======Append with reversed clause order:\n") < 0) return -1;
	pl_goal_solve(p, g1, test_p2, var_name_map);
	return 0;
}

static int pl_test2(prolog_t *p) {
	assert(p);
	static const char *database = 
		"app(nil,X,X). "
		"app(cons(X,L),M,cons(X,N)) :- app(L,M,N). "
		"man(bob). man(socrates). woman(alice). mortal(X) :- man(X). mortal(X) :- woman(X)." ;
	static const char *queries[] = {
		"?- app(I,J,cons(a,cons(b,cons(c,nil)))).",
		"?- mortal(socrates).",
		"?- mortal(bob).",
		"?- mortal(alice).",
		"?- mortal(god).",
		"?- mortal(X).",
		"?- man(X).",
		"?- woman(X).",
		"?- man(Y), woman(X).",
		"?- man(X), woman(X).",
		"?- man(X), mortal(X).",
		"?- man(Y), mortal(X).",
		/*"? X(alice).",*/
	};
	const size_t count = NELEMS(queries);

	if (pl_eval_string(p, database) < 0)
		return -1;
	for (size_t i = 0; i < count; i++) {
		uint8_t buf[128] = { 0, };
		if (pl_putf(p, buf, sizeof buf, "\n======= Query #%d '%s'\n", (int)i, queries[i]) < 0)
			return -1;
		if (pl_eval_string(p, queries[i]) < 0)
			return -1;
	}
	return 0;
}


typedef struct {
	char *arg;   /* parsed argument */
	int index,   /* index into argument list */
	    option,  /* parsed option */
	    reset;   /* set to reset */
	char *place; /* internal use: scanner position */
	int  init;   /* internal use: initialized or not */
	FILE *error; /* turn error reporting on/off */
} pl_getopt_t;   /* getopt clone; with a few modifications */

/* Adapted from: <https://stackoverflow.com/questions/10404448>, this
 * could be extended to parse out numeric values, and do other things, but
 * that is not needed here. The function and structure should be turned
 * into a header only library. */
static int pl_getopt(pl_getopt_t *opt, const int argc, char *const argv[], const char *fmt) {
	assert(opt);
	assert(fmt);
	assert(argv);
	enum { BADARG_E = ':', BADCH_E = '?', BADIO_E = '!', };

	if (!(opt->init)) {
		opt->place = ""; /* option letter processing */
		opt->init  = 1;
		opt->index = 1;
	}

	if (opt->reset || !*opt->place) { /* update scanning pointer */
		opt->reset = 0;
		if (opt->index >= argc || *(opt->place = argv[opt->index]) != '-') {
			opt->place = "";
			return -1;
		}
		if (opt->place[1] && *++opt->place == '-') { /* found "--" */
			opt->index++;
			opt->place = "";
			return -1;
		}
	}

	const char *oli = NULL; /* option letter list index */
	if ((opt->option = *opt->place++) == ':' || !(oli = strchr(fmt, opt->option))) { /* option letter okay? */
		 /* if the user didn't specify '-' as an option, assume it means -1.  */
		if (opt->option == '-')
			return -1;
		if (!*opt->place)
			opt->index++;
		if (opt->error && *fmt != ':')
			if (fprintf(opt->error, "illegal option -- %c\n", opt->option) < 0)
				return BADIO_E;
		return BADCH_E;
	}

	if (*++oli != ':') { /* don't need argument */
		opt->arg = NULL;
		if (!*opt->place)
			opt->index++;
	} else {  /* need an argument */
		if (*opt->place) { /* no white space */
			opt->arg = opt->place;
		} else if (argc <= ++opt->index) { /* no arg */
			opt->place = "";
			if (*fmt == ':')
				return BADARG_E;
			if (opt->error)
				if (fprintf(opt->error, "option requires an argument -- %c\n", opt->option) < 0)
					return BADIO_E;
			return BADCH_E;
		} else	{ /* white space */
			opt->arg = argv[opt->index];
		}
		opt->place = "";
		opt->index++;
	}
	return opt->option; /* dump back option letter */
}

static int pl_help(FILE *out, const char *arg0) {
	assert(out);
	assert(arg0);

	return fprintf(out, 
		"Usage: %s \n\n"
		"Project: A tiny Prolog interpreter.\n"
		"License: " PL_LICENSE "\n"
		"Author:  " PL_AUTHOR "\n"
		"Repo:    " PL_REPO "\n"
		"Email:   " PL_EMAIL "\n"
		"Version: " PL_VERSION "\n"
		"\nOptions:\n"
		"\t-h, display this help message and quit.\n"
		"\t-o key=value. set an option.\n"
		"\t-t, run built in tests.\n"
		"\t-p, read program from stdin and execute query.\n"
		"\nThis program return non-zero on error.\n\n"
		"This program is a reimplementation of a prolog interpreter available\n"
		"at <https://www.cl.cam.ac.uk/~am21/research/funnel/prolog2020.cpp>,\n"
		"with a paper here <https://www.cl.cam.ac.uk/~am21/papers/wflp00.pdf>,\n"
		"by Alan Mycroft. This program adds more functionality, a primitive garbage\n"
		"collector and a parser for the language.\n\n"
		"Examples:\n\n"
		"\tman(bob).\n"
		"\tman(socrates).\n"
		"\tmortal(X) :- man(X).\n"
		"\t? mortal(socrates).\n"
		"\nThe grammar is:\n\n"
		"\tid      := atom\n"
		"\tterm    := var | [ atom { '(' rule ')' } ]\n"
		"\trule    := term { ',' term }\n"
		"\tclause  := term [ ':-' rule ]\n"
		"\tgoal    := '?-' rule\n"
		"\tprogram := { [ goal | clause ] '.' } EOF\n\n",


		arg0);
}

static int pl_deinit(prolog_t *p) {
	assert(p);
	pl_sweep(p); /* clear all set flags */
	pl_sweep(p);
	pl_release(p, p->gc);
	pl_release(p, p->lex.buf);
	pl_release(p, p->stack);
	p->lex.used = 0;
	p->lex.length = 0;
	p->gc = NULL;
	p->stack = NULL;
	p->db = NULL;
	p->tail = NULL;
	return 0;
}

static int pl_flag(const char *v) {
	static char *y[] = { "yes", "on", "true", };
	static char *n[] = { "no",  "off", "false", };
	for (size_t i = 0; i < NELEMS(y); i++) {
		if (!strcmp(y[i], v))
			return 1;
		if (!strcmp(n[i], v))
			return 0;
	}
	return -1;
}

static int pl_set_option(prolog_t *s, char *kv) {
	assert(s);
	assert(kv);
	char *k = kv, *v = NULL;
	if ((v = strchr(kv, '=')) == NULL || *v == '\0') {
		return -1;
	}
	*v++ = '\0';
	if (!strcmp(k, "depth")) { s->maxlevel = atol(v); return 0; }
	const long r = pl_flag(v);
	if (r < 0) return -1;
	if (!strcmp(k, "gc"))     { pl_set_flag(&s->sysflags, PL_SFLAG_GC_OFF_E, !r); } 
	else if (!strcmp(k, "parse-debug")) { pl_set_flag(&s->sysflags, PL_SFLAG_PARSER_DEBUG, r); }
	else if (!strcmp(k, "reverse")) { pl_set_flag(&s->sysflags, PL_SFLAG_REVERSE_PROGRAM_ORDER, r); }
	else if (!strcmp(k, "terse")) { pl_set_flag(&s->sysflags, PL_SFLAG_PRINT_ONLY_MATCHES, r); }
	else if (!strcmp(k, "novar")) { pl_set_flag(&s->sysflags, PL_SFLAG_ONLY_PRINT_YES_ON_MATCH, r); }
	else { return -2; }
	return 0;
}

// TODO: Print out memory stats, custom arena, ...
int main(int argc, char **argv) {
	prolog_t prolog = { .alloc = pl_alloc_cb, .put = pl_put_file_cb, .get = pl_get_file_cb, .in = stdin, .out = stdout, .prompt = "> ", }, *p = &prolog;
	pl_getopt_t opt = { .init = 0, .error = stderr, };

	for (int ch = 0; (ch = pl_getopt(&opt, argc, argv, "htlpP:r:o:")) != -1; ) {
		switch (ch) {
		case 'h': return pl_help(stderr, argv[0]) < 0;
		case 't': {
			const int r1 = pl_test1(p);
			pl_reset(p);
			const int r2 = pl_test2(p);
			pl_deinit(p);
			return r1 < 0 || r2 < 0;
		}
		case 'o': {
			if (pl_set_option(p, opt.arg) < 0) {
				(void)fprintf(stderr, "invalid option argument -- %s\n", opt.arg);
				return 1;
			}
			break;
		}
		case 'r': {
			p->maxlevel = atoi(opt.arg);
			break;
		}
		case 'l': {
			for (int l = 0; (l = pl_lexer(p)) != PLEX_EOF;) {
				const bool named = l == PLEX_ATOM || l == PLEX_VAR;
				char *b = named ? (char*)p->lex.buf : "";
				if (fprintf(p->out, "lex %c/%s\n", l, b) < 0)
					return 1;
			}
			return 0;
		}
		case 'p': {
			const int r = pl_eval_file(p, stdin);
			/*pl_program_t *program = NULL;
			pl_goal_t *goal = NULL;
			pl_term_var_mapping_t *map = pl_term_var_mapping_new(p, NULL, NULL, 0);
			pl_parse(p, map, &program, &goal);
			int r = 0;
			if (goal)
				r = pl_goal_solve(p, goal, program, map);*/
			pl_deinit(p);
			return r < 0;
		}
		case 'P': {
			const int r = pl_eval_string(p, opt.arg);
			pl_deinit(p);
			return r < 0;
		}
		default: return 1;
		}
	}
	return 0;
}
