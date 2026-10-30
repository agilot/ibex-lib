//============================================================================
//                                  I B E X
//
//                               ************
//                                 IbexQuery
//                               ************
//
// A persistent SMT-LIB 2 server for the Ibex optimizer, speaking the dialect
// dReal accepts: QF_NRA plus transcendental functions and the minimize/maximize
// commands. The point is to pay Ibex's compile+link cost once: spawn the
// process, keep it on a pipe, send it problems.
//
// License     : See the LICENSE file
//============================================================================
//
// INVOCATION
// ----------
//   ibexquery                 read commands from stdin (the pipe case)
//   ibexquery problem.smt2    run every command in a file, then exit
//   ibexquery a.smt2 b.smt2 - several files in order; '-' means stdin
//   ibexquery --watch p.smt2  run it now, then again on every save
//   --interval MS             how often --watch polls for changes (default 200)
//
// Replies go to stdout in every mode; progress notes, warnings and anything the
// library prints go to stderr, so redirecting stdout collects exactly the reply
// lines. (exit) means different things per mode, deliberately:
//   stdin   -- terminate.
//   files   -- stop there, skipping any remaining files.
//   --watch -- end that pass only; watching continues, because one stray (exit)
//              in an edited file should not silently kill the watcher. A note
//              is written to stderr when this happens.
// Under --watch the whole solver state is reset before each pass, so a
// declaration deleted from the file is really gone rather than lingering from
// the run before. Unreadable input exits nonzero.
//
// WHY THIS DIALECT
// ----------------
// dReal's SMT2 grammar is the smallest standard-shaped language that says
// everything this server needs to hear. Plain SMT-LIB cannot: it has no
// objective (check-sat is yes/no) and no transcendental functions. dReal adds
// exactly those two things, and nothing else here is an invention:
//
//   commands   set-logic set-option set-info declare-fun declare-const
//              define-fun assert minimize maximize check-sat get-model
//              get-value get-objectives push pop reset reset-assertions
//              echo exit
//   terms      + - * / pow ^ sqrt exp log abs
//              sin cos tan asin acos atan atan2 sinh cosh tanh min max
//              let, and = < <= > >= and not true false in assertions
//
// Ibex covers that function set entirely. Three things dReal accepts are
// refused here, each because Ibex would have to answer a different question:
//
//   or, xor, =>   A disjunction. SystemFactory takes a conjunction of
//                 constraints and nothing else, so there is no way to accept
//                 one except by weakening it silently. Assert the cases
//                 separately with push/pop.
//   ite           The same disjunction wearing a term's clothes: (ite c a b)
//                 holds when (c and a) or ((not c) and b). It is also
//                 nonsmooth, so KKT and the linear relaxations would be working
//                 on a function with no derivative at the switch. dReal can do
//                 this because its SAT layer case-splits; there is no such
//                 layer here. Use min/max, or split the cases.
//   non-integer   pow(expr,double) expands to exp(y*log(x)), which silently
//   exponents     narrows the base to x>0.
//
// SEMANTICS: REALS, NOT FLOATS
// ----------------------------
// Every term is interpreted over the reals, which is what QF_NRA means and what
// Ibex computes. A literal denotes an exact real number and is enclosed, never
// rounded to it: SMT-LIB says 0.1 is the rational 1/10, so reading it as the
// nearest double would substitute 0.1000000000000000055511151231257827 for the
// number the client wrote. For a client that is a proof assistant, that is a
// soundness bug rather than a rounding detail, and Ibex itself does exactly
// that -- Interval(double,double) stores the two doubles it is handed
// (ibex_Interval.h:886) and the Minibex lexer builds constants with atof
// (parser/lexer.l:123). See NUMBERS.
//
// This server therefore says nothing about floating-point programs. If a client
// wants to bound a rounding error, it must model the rounded value as its own
// variable and relate it to the exact one with an assertion; asking about the
// float semantics of the term itself is not a question this server answers.
//
// Functions are partial: a point where a term is undefined, such as (log x) at
// x<=0 or a division by zero, is not a solution. An objective undefined on every
// feasible point therefore answers unsat.
//
// PROTOCOL
// --------
// One S-expression per command, replies on stdout in SMT-LIB shape. Commands
// that succeed silently in SMT-LIB reply "success" only while :print-success is
// on; it is OFF by default here, matching dReal and keeping a pipe quiet.
//
//   (set-logic QF_NRA)              also QF_LRA, QF_NIA, QF_LIA -- see below
//   (declare-const x Real)          declare a variable
//   (declare-fun x () Real)         the same thing, spelled the long way
//   (define-fun f ((a Real)) Real <term>)     name a term
//   (assert <formula>)
//   (minimize <term>) | (maximize <term>)     sets THE objective, replacing
//   (check-sat)                     -> sat | unsat | unknown
//   (get-objectives)                -> the enclosure of the optimum
//   (get-model)                     -> the point that certifies it
//   (get-value (<term>...))         -> that point's coordinates
//   (push [n]) (pop [n])            scope declarations and assertions
//   (reset) (reset-assertions) (echo "...") (exit) (get-option :k)
//   (set-option :k v) (set-info :k v)
//
// Sorts: Real only. Int is refused rather than silently relaxed -- Ibex has no
// integrality constraint here, so accepting (declare-const n Int) would answer a
// different problem than the one asked. The integer logics are accepted by
// set-logic because a client may announce one before discovering that, and the
// refusal is better raised at the declaration that actually needs it.
// Uninterpreted functions are refused: (declare-fun f (Real) Real) has no
// meaning Ibex can give it.
//
// STATE
// -----
// The server is stateful, as SMT-LIB requires: declarations, definitions and
// assertions accumulate, and (check-sat) solves whatever has accumulated. This
// is the one real difference from a one-shot query protocol, and it is what
// lets a client push a variation, test it, and pop back.
//
// (push n) opens n scopes; (pop n) closes them, undoing every declaration,
// definition and assertion made inside -- including the objective, which is
// restored to whatever it was on entry. (reset-assertions) empties the assertion
// stack and keeps declarations; (reset) returns the process to a fresh start.
//
// REPLIES
// -------
//   sat | unsat | unknown              from (check-sat)
//   (objectives (<obj> <lo> <hi>))     from (get-objectives)
//   ((define-fun x () Real <v>) ...)   from (get-model)
//   ((<term> <v>) ...)                 from (get-value ...)
//   (:ibex-enclosure ((x <lo> <hi>) ...))   from (get-info :ibex-enclosure)
//   (error "<message>")                anything the client got wrong
//   unsupported                        a well-formed command with no meaning here
//
// Every <v>, <lo> and <hi> above is a well-sorted term of sort Real, so a
// standard SMT-LIB reader parses every reply this server can emit. That costs
// three things worth naming, because the obvious spellings are all wrong:
//
//   4        is a <numeral>, sorted Int. The Reals theory has no Int-to-Real
//            coercion, so the value is written 4.0.
//   -1.5     is not a literal: SMT-LIB has no negative numbers, only unary
//            minus applied to a non-negative one. The value is written (- 1.5).
//   3e-08    has no SMT-LIB token at all -- a reader takes the decimal 3 and
//            then the symbol e-08. Written out in full as 0.00000003.
//
// (get-objectives) and (get-option) are extensions rather than standard forms,
// and an infinite bound is meaningful in both, so those two alone can answer
// +oo or -oo. Both are legal SMT-LIB symbols and tokenise like any other.
//
// The status mapping is the trap, and it is deliberate:
//
//   Optimizer::INFEASIBLE          -> unsat    a PROOF that no point satisfies
//                                              the assertions: Ibex emptied the
//                                              search space.
//   Optimizer::SUCCESS             -> sat      a point was found AND the optimum
//                                              was bracketed to the tolerances.
//   Optimizer::UNBOUNDED_OBJ       -> sat      a point was found and the objective
//                                              has no finite bound, so
//                                              get-objectives reports an infinite
//                                              endpoint. Without a point this is
//                                              unknown: the status alone does not
//                                              prove feasibility.
//   NO_FEASIBLE_FOUND, TIME_OUT,
//   UNREACHED_PREC                 -> unknown  nothing was proved either way.
//
// "unsat" and "unknown" are therefore NOT interchangeable, and a client must not
// read "not unsat" as "satisfiable". dReal answers delta-sat where this server
// answers sat, because the two are proving different things: dReal certifies a
// delta-relaxation of the formula, Ibex brackets an optimum. Both are honest and
// neither implies the other, so no attempt is made to reuse dReal's word for it.
//
// NUMBERS -- how literals are read
// --------------------------------
// SMT-LIB fixes the meaning of every literal, so no wrapper syntax is needed and
// none is invented. Each one denotes an exact real, and each is turned into an
// interval that ENCLOSES it:
//
//   form            value          how
//   ------------------------------------------------------------------
//   <numeral>       n              exact; refused above 2^53, where the
//                                  int-to-double conversion drops bits
//   <decimal>       m*10^-k        enclosed by Interval(m)/pow([10],k)
//   0x1.8p3         m*2^e          enclosed by Interval(m)*pow([2],e)
//   (/ p q)         p/q            just division; Ibex rounds it outward
//   (- a)           -a             exactness of a is preserved
//
// Nothing here rounds to nearest, so nothing can put a value in front of Ibex
// that is not the number the client wrote. That is the whole reason the decimal
// case is arithmetic rather than a strtod call. A mantissa above 2^53 is enclosed
// the same way, and a literal beyond the double range is refused, because it has
// no finite enclosure.
//
// The enclosures are computed with Ibex's own outward-rounded arithmetic because
// Ibex has no exact rational type. Computing m/(double)10^k in C++ and wrapping
// the result would round once, to nearest, before Ibex ever saw it, and the
// enclosure property would be gone. Verified here: interval / and * round
// outward (Interval(1)/Interval(3) comes back one ulp wide) and pow(Interval,int)
// handles negative exponents. Dividing by the positive power of ten rather than
// multiplying by the negative one keeps the denominator exact up to 10^22 and
// leaves a single outward-rounded operation, so 0.5 comes back exact rather than
// two ulps wide.
//
// Ibex offers no rigorous decimal-string-to-interval parsing. The gaol backend
// does -- gaol::interval("0.1") is documented to return [0.09999,0.10001] -- but
// it is not reachable through Ibex's Interval interface, and using it would
// hard-code this file to gaol and break the bias, filib and direct backends that
// interval_lib_wrapper/ also supports. Hence the arithmetic route above.
//
// One trap worth naming: gaol leaves the FPU in round-toward-+oo permanently,
// and strtod honours the mode, so the few conversions that are allowed to round
// to nearest are wrapped in a guard that switches the mode and puts gaol's back.
// Those conversions are exactly the ones whose result is not part of a rigorous
// answer: option values (tolerances, timeout, seed), which tune the search
// rather than state the problem, and the digits printed in a reply.
//
// BOUNDS ARE LIFTED OUT OF ASSERTIONS
// -----------------------------------
// SMT-LIB has no notion of a variable's domain, but Ibex searches a box, and an
// unbounded box is both slower and weaker. So an assertion whose shape is a
// bound on one variable against a constant -- (<= 1 x), (< x 2), (<= 1 x 2) --
// tightens that variable's domain instead of becoming a constraint. Bounds are
// taken OUTWARD, so the search box encloses the asserted one, and anything that
// is not exactly that shape stays a constraint.
//
// A box endpoint is a single double and cannot exclude itself, so a strict bound
// is lifted AND kept as a constraint, where Ibex's own CmpOp records LT. A point
// on the boundary is therefore never reported as a model.
//
// OPTIONS
// -------
// SMT-LIB lets any :keyword carry a value, so tuning the search needs no new
// syntax. dReal's :precision is honoured, and the Ibex knobs are namespaced:
//
//   :precision <real>        dReal's delta; sets eps-x and eps-h together
//   :ibex-rel-eps-f :ibex-abs-eps-f :ibex-eps-x :ibex-eps-h        (real)
//   :ibex-timeout :ibex-random-seed                                (real)
//   :ibex-rigor :ibex-kkt :print-success                           (bool)
//   :ibex-trace :ibex-simpl-level                                  (int)
//
// Options persist until changed, unlike a per-query setting, because that is
// what set-option means. ":ibex-timeout" <= 0 disables the limit, matching
// Ibex's own convention. The others map onto OptimizerConfig /
// DefaultOptimizerConfig setters of the same name.
//
// MODELS
// ------
// (get-model) reports one value per declared variable, printed with enough
// digits to round-trip through strtod. This is the point Ibex found that
// CERTIFIES the achievable side of the bound reported by (get-objectives). It is
// NOT a claim about where the true optimum lies: the true argmin may be
// somewhere else entirely, and all that is asserted is that this point satisfies
// the assertions and attains this value.
//
// In rigor mode Ibex certifies a box rather than a point, and a box has no
// SMT-LIB value form. (get-model) reports the midpoint, which is a
// REPRESENTATIVE and not itself certified; the bounds Ibex proved are served by
// (get-info :ibex-enclosure), and that is the reply to read when the guarantee
// is the point of the run. Its bounds are stepped one ULP outward before
// printing, so a client doing exact decimal arithmetic still holds a superset of
// the certified box rather than a subset of it. Outside rigor mode the box is
// degenerate and the two replies agree to within that rounding.
//
// "Satisfies" carries Ibex's own caveat: an equality h(x)=0 is relaxed to
// |h(x)|<=eps-h (1e-8 by default), so by default the model only satisfies
// equalities to that tolerance, and the achievable bound can land just past the
// true optimum. Minimizing (x-1)^2+(y-2)^2 under x+y=1 (optimum exactly 2)
// reports an upper bound of 1.999999982 by default and 2.0000000000000004 under
// :ibex-rigor true. Use rigor -- or inequalities -- when a problem has
// equalities and the bound has to hold.
//
// EXPRESSION SHARING
// ------------------
// 'let' and 'define-fun' both bind terms that have already been built, so a body
// mentioning a name four times shares one subexpression rather than rebuilding
// it (measured on the previous protocol: 8 DAG nodes against 20 for the
// written-out form).
//
// That sharing is structural, and structure alone would not be worth much: an
// evaluator that walks the expression as a tree re-visits a shared node once per
// mention, so a name used n times costs n times as much and nothing has been
// saved. Ibex does not do that. Function compiles to ExprSubNodes, in which
// "each sub-node appears only once", and CompiledFunction::forward/backward are
// single linear passes over that array, so every node is evaluated exactly once
// per sweep however many parents point at it. Sharing is therefore shared WORK,
// and bindings nest for free: a ladder of five doublings-of-doublings, whose
// tree form would have 4^256 leaves, has 386 DAG nodes and solves in 40 ms.
// (Kodiak's server shares structure but evaluates as a tree, so the same ladder
// does not terminate there; its 'let' exists to work around that. The two
// servers agree on syntax here and disagree completely on cost.)
//
// Two costs ARE worth knowing about, and neither is evaluation. Both are
// quadratic, and they are independent -- measured with a deep chain, at loose
// and tight precision, so the search is not what is being timed:
//
//   1. Building. Every ExprNode constructor calls ExprSize(), which walks the
//      whole sub-DAG to recompute the node count, so assembling an n-node
//      expression is O(n^2). Nothing to do with let -- a plain binding-free
//      chain scales the same way -- and it is invisible below a few thousand
//      nodes (386 nodes build in 7 ms), but a machine-generated problem with
//      tens of thousands will crawl.
//
//   2. Symbolic differentiation, when KKT is on. DefaultOptimizerConfig enables
//      KKT for UNCONSTRAINED problems (set_kkt(sys.nb_ctr==0)), and
//      CtcKuhnTucker builds a symbolic derivative through ExprDiff. Chain-rule
//      differentiation of an n-deep composition yields an O(n^2) derivative
//      whatever the implementation, so this bites in proportion to derivative
//      size, not node count: a 16384-node chain of sin/cos costs 22.7 s, the
//      same-sized chain of additions 1.1 s. (set-option :ibex-kkt false) removes
//      it entirely and makes the trig chain LINEAR -- 0.06 s, a 380x difference
//      -- because the numeric path never builds a symbolic derivative at all:
//      Gradient is reverse-mode AD over the compiled node array, summing
//      adjoints with g[x1] += g[y]. The default is left matching ibexopt rather
//      than quietly diverging from it; turn KKT off for deep compositions.
//
// Sharing survives differentiation, which is the non-obvious half: ExprDiff
// keeps a NodeMap<const ExprNode*> of per-node gradients rather than
// re-descending, so the ladder above stays flat with KKT on (386 nodes, 4^256
// tree paths, 40 ms). A differentiator that walked the tree would re-visit a
// shared node once per PATH and die there -- which is what Kodiak does, and the
// real reason its 'let' is load-bearing. Deep chains hurt both servers; shared
// DAGs hurt only that one.
//
// SCOPING
// -------
// 'let' is SMT-LIB's: bindings in one let are evaluated in the ENCLOSING scope
// and take effect simultaneously, so (let ((x y) (y x)) ...) swaps rather than
// aliases, and nested lets chain outward. A define-fun body is different: it
// sees its own parameters and the global declarations, never the caller's
// bindings. Given (define-fun inner ((p Real)) Real (* p 2)) and
// (define-fun outer ((p Real) (q Real)) Real (inner q)), the call (outer x y) is
// 2*y -- if frames chained it would silently be 2*x. Parameters shadow globals
// of the same name, and let-bindings shadow both.
//
// Redefining a name is refused, as SMT-LIB requires; pop a scope to reuse it.
// Circular definitions are refused with the chain ("definition 'f' is circular:
// f -> g -> f"), and a failure inside a body says which definition it came from
// ("in definition 'f': unknown function 'frobnicate'"), because the calling
// command usually looks fine on its own. Definition names may not be reserved
// words; parameter names may be, since parameters are only ever looked up as
// bare atoms while functions are only ever list heads.
//
// STDOUT
// ------
// Ibex writes to stdout when tracing (Optimizer::update_loup) and in
// Optimizer::report; SoPlex and gaol may too. Before anything else, main() dups
// the real stdout aside and points fd 1 at stderr, so no library write can
// corrupt the protocol stream. Replies go to the saved descriptor.
//
// LIMITATION
// ----------
// ibex_error() calls exit(-1) (ibex_Exception.cpp:20) and no handler can stop
// it. Commands are validated before Ibex sees them wherever that is possible,
// and ibex::Exception is caught, but a library-internal ibex_error will still
// take the process down. So will a chain of many thousands of definitions, which
// overflows the stack (measured: from about 8000 links).
//============================================================================

#include "ibex.h"
#include "parse_args.h"

#include <cctype>
#include <cerrno>
#include <cfenv>
#include <climits>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

#include <fcntl.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

using namespace std;
using namespace ibex;

namespace {

/*============================ replies ===================================*/

/* The real stdout, saved before fd 1 is pointed at stderr. */
int reply_fd = STDOUT_FILENO;

void reply(const string& line) {
	string out = line;
	out += '\n';
	size_t off = 0;
	while (off < out.size()) {
		ssize_t n = write(reply_fd, out.data() + off, out.size() - off);
		if (n < 0) {
			if (errno == EINTR) continue;
			return; // client is gone; the next read will end the loop
		}
		off += (size_t) n;
	}
}

/* gaol leaves the FPU in round-toward-+oo for the whole process, and strtod
 * obeys the mode: under it, "%.17g" of a double does not parse back to that
 * double (measured: ~99.6% of random doubles fail). Every decimal conversion
 * therefore runs in round-to-nearest, restoring gaol's mode afterwards --
 * leaving it on nearest would silently un-round the interval arithmetic. */
class NearestRounding {
public:
	NearestRounding() : saved(fegetround()) { fesetround(FE_TONEAREST); }
	~NearestRounding() { fesetround(saved); }
private:
	int saved;
};

/* "%g" reaches for exponent notation, which SMT-LIB has no token for at all: a
 * reader tokenising 2.999999991e-08 gets the decimal 2.999999991 followed by the
 * symbol e-08, and one tokenising 4e+20 gets a numeral abutting a symbol. Shift
 * the point by hand instead. Only digits move, so nothing is rounded here. */
string without_exponent(const string& g) {
	size_t e = g.find_first_of("eE");
	if (e == string::npos) return g;

	string mant = g.substr(0, e);
	int exp = atoi(g.c_str() + e + 1);

	string sign;
	if (!mant.empty() && (mant[0] == '-' || mant[0] == '+')) {
		if (mant[0] == '-') sign = "-";
		mant.erase(0, 1);
	}

	size_t dot = mant.find('.');
	int point = dot == string::npos ? (int) mant.size() : (int) dot;
	if (dot != string::npos) mant.erase(dot, 1);
	point += exp;

	if (point <= 0)
		return sign + "0." + string((size_t) -point, '0') + mant;
	if ((size_t) point >= mant.size())
		return sign + mant + string((size_t) point - mant.size(), '0') + ".0";
	return sign + mant.substr(0, (size_t) point) + "." + mant.substr((size_t) point);
}

/* Shortest representation that still round-trips, so a client can recover the
 * exact double we computed with, written as an SMT-LIB <decimal>: digits, a
 * point, digits. The point is not decoration. A bare 4 is a <numeral>, which
 * the Reals theory sorts as Int and does not coerce, so a well-sorted reply has
 * to say 4.0. Sign is not handled here -- see smt_real. */
string decimal(double x) {
	if (x == 0) return "0.0"; // both zeros print the same; the sign is not information here
	NearestRounding nearest;
	char buf[64];
	string g;
	for (int prec = 15; prec < 17 && g.empty(); prec++) {
		snprintf(buf, sizeof(buf), "%.*g", prec, x);
		if (strtod(buf, NULL) == x) g = buf;
	}
	if (g.empty()) {
		snprintf(buf, sizeof(buf), "%.17g", x);
		g = buf;
	}
	g = without_exponent(g);
	if (g.find('.') == string::npos) g += ".0";
	return g;
}

/* A finite double as a well-sorted term of sort Real. SMT-LIB has no negative
 * literals: the '-' in -1.5 is not part of the token, so a value that can be
 * negative has to be written as an application of unary minus. */
string smt_real(double x) {
	if (x < 0) return "(- " + decimal(-x) + ")";
	return decimal(x);
}

/* Payload of the two replies that are extensions rather than standard forms
 * ((get-objectives) and (get-option)), where an infinite bound is meaningful
 * and there is no sort obligation to meet. +oo and -oo are legal SMT-LIB
 * symbols, so they still tokenise. */
string fmt(double x) {
	if (x == POS_INFINITY) return "+oo";
	if (x == NEG_INFINITY) return "-oo";
	return smt_real(x);
}

/* Raised for anything the client got wrong; never escapes handle(). */
struct ProtocolError {
	string msg;
	explicit ProtocolError(const string& m) : msg(m) { }
};

/* Raised for a well-formed command this server has no meaning for. SMT-LIB
 * spells that "unsupported", and it is a different answer from an error. */
struct Unsupported { };

/*========================= S-expression reader ==========================*/

struct Sexp {
	bool is_atom;
	bool is_string; // an atom that came from "..."; never confusable with a symbol
	string atom;    // for a string, the decoded contents
	vector<Sexp> list;

	Sexp() : is_atom(false), is_string(false) { }

	bool sym_is(const char* s) const {
		return is_atom && !is_string && atom == s;
	}
};

typedef enum { FORM_OK, FORM_EOF, FORM_INCOMPLETE, FORM_ERROR } FormStatus;

/* Bounds recursion in read() so that a pathological "(((((..." cannot take the
 * process down through the stack rather than through an error reply. */
const int MAX_DEPTH = 256;

bool is_delim(char c) {
	return isspace((unsigned char) c) || c == '(' || c == ')'
	    || c == ';' || c == '"' || c == '|';
}

/* Symbols are stored decoded, so a reply has to restore the bars of any symbol
 * that needed them: (define-fun a b () Real 0.0) is not a well-formed reply. */
string smt_symbol(const string& s) {
	for (size_t i = 0; i < s.size(); i++)
		if (is_delim(s[i])) return "|" + s + "|";
	return s;
}

class Reader {
public:
	Reader(const string& text) : s(text), i(0) { }

	FormStatus next(Sexp& out, string& err) {
		skip_blanks();
		if (i >= s.size()) return FORM_EOF;
		if (s[i] == ')') {
			// Swallow the whole run: the tail of a form that was rejected
			// mid-way would otherwise produce one error line per ')'.
			while (i < s.size() && s[i] == ')') { i++; skip_blanks(); }
			err = "unexpected ')'";
			return FORM_ERROR;
		}
		return read(out, err, 0);
	}

	/* Bytes consumed so far: lets the stdin loop drop what it has handled. */
	size_t offset() const { return i; }

private:
	const string& s;
	size_t i;

	void skip_blanks() {
		while (i < s.size()) {
			if (isspace((unsigned char) s[i])) i++;
			else if (s[i] == ';') { while (i < s.size() && s[i] != '\n') i++; }
			else break;
		}
	}

	/* SMT-LIB string: "..." with "" standing for a literal quote. */
	FormStatus read_string(Sexp& out, string& err) {
		i++; // opening quote
		out.is_atom = true;
		out.is_string = true;
		out.atom.clear();
		out.list.clear();
		for (;;) {
			if (i >= s.size()) return FORM_INCOMPLETE;
			if (s[i] == '"') {
				if (i + 1 < s.size() && s[i+1] == '"') { out.atom += '"'; i += 2; continue; }
				if (i + 1 >= s.size()) {
					// Could be the close, or the first half of an escape that
					// has not arrived yet. Only more input can tell.
					return FORM_INCOMPLETE;
				}
				i++;
				return FORM_OK;
			}
			out.atom += s[i++];
		}
		(void) err;
	}

	/* SMT-LIB quoted symbol: |anything but | and backslash|. Kept as a plain
	 * symbol once decoded, which is what the standard says it is. */
	FormStatus read_quoted_symbol(Sexp& out, string& err) {
		i++; // opening bar
		out.is_atom = true;
		out.is_string = false;
		out.atom.clear();
		out.list.clear();
		for (;;) {
			if (i >= s.size()) return FORM_INCOMPLETE;
			if (s[i] == '\\') {
				err = "'\\' is not allowed inside |...|";
				// Resume past the closing bar, or it would open a new symbol that
				// swallows the commands after it.
				while (i < s.size() && s[i] != '|') i++;
				if (i < s.size()) i++;
				return FORM_ERROR;
			}
			if (s[i] == '|') { i++; return FORM_OK; }
			out.atom += s[i++];
		}
	}

	FormStatus read(Sexp& out, string& err, int depth) {
		if (depth > MAX_DEPTH) {
			err = "expression nested too deeply";
			return FORM_ERROR;
		}
		skip_blanks();
		if (i >= s.size()) return FORM_INCOMPLETE;

		if (s[i] == ')') {
			i++;
			err = "unexpected ')'";
			return FORM_ERROR;
		}

		if (s[i] == '"') return read_string(out, err);
		if (s[i] == '|') return read_quoted_symbol(out, err);

		if (s[i] == '(') {
			i++;
			out.is_atom = false;
			out.is_string = false;
			out.list.clear();
			for (;;) {
				skip_blanks();
				if (i >= s.size()) return FORM_INCOMPLETE;
				if (s[i] == ')') { i++; return FORM_OK; }
				out.list.push_back(Sexp());
				FormStatus st = read(out.list.back(), err, depth + 1);
				if (st != FORM_OK) return st;
			}
		}

		size_t start = i;
		while (i < s.size() && !is_delim(s[i])) i++;
		out.is_atom = true;
		out.is_string = false;
		out.atom = s.substr(start, i - start);
		out.list.clear();
		return FORM_OK;
	}
};

/* Whole-text scan used by --watch to tell a half-written file (INCOMPLETE)
 * from one that is merely wrong (ERROR), without betting on a settle delay. */
FormStatus scan_all(const string& text, vector<Sexp>& forms, string& err) {
	Reader r(text);
	forms.clear();
	for (;;) {
		Sexp form;
		FormStatus st = r.next(form, err);
		if (st == FORM_EOF) return FORM_OK;
		if (st != FORM_OK) return st;
		forms.push_back(form);
	}
}

/*============================== numbers =================================*/

/* Largest integer above which int-to-double conversion starts dropping bits. */
const long long MAX_EXACT_INT = 1LL << 53;

/* Splits a decimal literal into mantissa and base-10 exponent. Returns false if
 * the text is not a decimal at all. 'overflow' means the mantissa did not fit,
 * so the literal cannot be enclosed by this route (never that it is wrong). */
bool scan_decimal(const string& t, unsigned long long& mantissa, long& exp10,
                  bool& neg, bool& overflow) {
	const unsigned long long LIMIT = (~(unsigned long long) 0 - 9) / 10;
	size_t i = 0;
	mantissa = 0; exp10 = 0; neg = false; overflow = false;

	if (i < t.size() && (t[i] == '+' || t[i] == '-')) { neg = (t[i] == '-'); i++; }

	int ndigits = 0; long nfrac = 0;
	while (i < t.size() && isdigit((unsigned char) t[i])) {
		if (mantissa > LIMIT) overflow = true;
		else mantissa = mantissa * 10 + (unsigned) (t[i] - '0');
		ndigits++; i++;
	}
	if (i < t.size() && t[i] == '.') {
		i++;
		while (i < t.size() && isdigit((unsigned char) t[i])) {
			if (mantissa > LIMIT) overflow = true;
			else mantissa = mantissa * 10 + (unsigned) (t[i] - '0');
			ndigits++; nfrac++; i++;
		}
	}
	if (ndigits == 0) return false;

	if (i < t.size() && (t[i] == 'e' || t[i] == 'E')) {
		i++;
		bool eneg = false;
		if (i < t.size() && (t[i] == '+' || t[i] == '-')) { eneg = (t[i] == '-'); i++; }
		if (i >= t.size() || !isdigit((unsigned char) t[i])) return false;
		long e = 0;
		while (i < t.size() && isdigit((unsigned char) t[i])) {
			if (e < 100000) e = e * 10 + (t[i] - '0');
			i++;
		}
		exp10 = eneg ? -e : e;
	}
	if (i != t.size()) return false;
	exp10 -= nfrac;
	return true;
}

/* Same for a hex float. Base 16 is a power of two, so the exponent is exact and
 * only the mantissa can overflow the accumulator. */
bool scan_hex(const string& t, unsigned long long& mantissa, long& exp2,
              bool& neg, bool& overflow) {
	const unsigned long long LIMIT = (~(unsigned long long) 0 - 15) / 16;
	size_t i = 0;
	mantissa = 0; exp2 = 0; neg = false; overflow = false;

	if (i < t.size() && (t[i] == '+' || t[i] == '-')) { neg = (t[i] == '-'); i++; }
	if (i + 1 >= t.size() || t[i] != '0' || (t[i+1] != 'x' && t[i+1] != 'X')) return false;
	i += 2;

	int ndigits = 0; long nfrac = 0;
	while (i < t.size() && isxdigit((unsigned char) t[i])) {
		if (mantissa > LIMIT) overflow = true;
		else mantissa = mantissa * 16 + (unsigned) (isdigit((unsigned char) t[i])
		                ? t[i] - '0' : (tolower(t[i]) - 'a' + 10));
		ndigits++; i++;
	}
	if (i < t.size() && t[i] == '.') {
		i++;
		while (i < t.size() && isxdigit((unsigned char) t[i])) {
			if (mantissa > LIMIT) overflow = true;
			else mantissa = mantissa * 16 + (unsigned) (isdigit((unsigned char) t[i])
			                ? t[i] - '0' : (tolower(t[i]) - 'a' + 10));
			ndigits++; nfrac++; i++;
		}
	}
	if (ndigits == 0) return false;

	if (i < t.size() && (t[i] == 'p' || t[i] == 'P')) {
		i++;
		bool eneg = false;
		if (i < t.size() && (t[i] == '+' || t[i] == '-')) { eneg = (t[i] == '-'); i++; }
		if (i >= t.size() || !isdigit((unsigned char) t[i])) return false;
		long e = 0;
		while (i < t.size() && isdigit((unsigned char) t[i])) {
			if (e < 100000) e = e * 10 + (t[i] - '0');
			i++;
		}
		exp2 = eneg ? -e : e;
	}
	if (i != t.size()) return false;
	exp2 -= 4 * nfrac; // each hex fraction digit is four binary places
	return true;
}

bool is_numeral(const string& t) {
	if (t.empty()) return false;
	size_t i = (t[0] == '+' || t[0] == '-') ? 1 : 0;
	if (i >= t.size()) return false;
	for (size_t k = i; k < t.size(); k++)
		if (!isdigit((unsigned char) t[k])) return false;
	return true;
}

bool looks_numeric(const string& s) {
	if (s.empty()) return false;
	size_t i = (s[0] == '+' || s[0] == '-') ? 1 : 0;
	return i < s.size() && (isdigit((unsigned char) s[i]) || s[i] == '.');
}

/* An integer, exactly. Beyond 2^53 the int-to-double conversion silently drops
 * bits, so the exactness promise would be a lie: reject instead. */
long long integer_text(const string& t, const char* what) {
	if (!is_numeral(t))
		throw ProtocolError(string(what) + ": not an integer: '" + t + "'");
	errno = 0;
	char* end = NULL;
	long long n = strtoll(t.c_str(), &end, 10);
	if (errno == ERANGE || *end != '\0' || n > MAX_EXACT_INT || n < -MAX_EXACT_INT)
		throw ProtocolError(string(what) + ": integer '" + t + "' exceeds 2^53, beyond "
		                    "which it is not exactly a double; write it as a quotient");
	return n;
}

/* (double) m rounds above 2^53, so the two halves are converted exactly and
 * summed with Ibex's outward-rounded addition. */
Interval enclose_integer(unsigned long long m) {
	return Interval((double) (m >> 32)) * Interval(4294967296.0)
	     + Interval((double) (m & 0xFFFFFFFFULL));
}

/* Beyond the double range there is no finite enclosure, and an unbounded constant
 * leaves Ibex searching for a value it can never reach. */
Interval finite_literal(const Interval& v, const string& t) {
	if (v.is_unbounded()) throw ProtocolError("literal '" + t + "' exceeds the double range");
	return v;
}

/* Encloses the exact real the literal denotes. Every arithmetic step is Ibex's
 * own, so every step rounds outward; nothing here rounds to nearest. */
Interval parse_number_atom(const string& t) {
	unsigned long long m; long ex; bool neg, ovf;

	if (is_numeral(t)) {
		double n = (double) integer_text(t, "integer");
		return Interval(n, n);
	}

	if (scan_hex(t, m, ex, neg, ovf)) {
		if (ovf) throw ProtocolError("hexadecimal literal '" + t + "' has too many "
		                             "significant digits to be enclosed");
		if (ex < -100000 || ex > 100000)
			throw ProtocolError("exponent of '" + t + "' out of range");
		Interval v = enclose_integer(m);
		if (ex >= 0) v *= pow(Interval(2, 2), (int) ex);
		else         v /= pow(Interval(2, 2), (int) -ex);
		return finite_literal(neg ? -v : v, t);
	}

	if (scan_decimal(t, m, ex, neg, ovf)) {
		if (ovf) throw ProtocolError("decimal literal '" + t + "' has too many "
		                             "significant digits to be enclosed");
		if (ex < -100000 || ex > 100000)
			throw ProtocolError("exponent of '" + t + "' out of range");
		Interval v = enclose_integer(m);
		// pow(Interval,int) does handle negative exponents, but 10^-e is not a
		// double, so multiplying by it rounds twice and 0.5 -- which is exact --
		// would come back two ulps wide. Dividing by the positive power keeps the
		// denominator exact up to 10^22 and leaves one outward-rounded operation.
		if (ex >= 0) v *= pow(Interval(10, 10), (int) ex);
		else         v /= pow(Interval(10, 10), (int) -ex);
		return finite_literal(neg ? -v : v, t);
	}

	throw ProtocolError("not a number: '" + t + "'");
}

/* Option values take a plain nearest-rounded decimal, unlike everything else:
 * they tune the search rather than state the problem, so they carry no rigorous
 * guarantee and an enclosure would only be noise. */
double parse_plain_double(const Sexp& e, const char* what) {
	const char* PLAIN = " takes a plain decimal (options are search tolerances, "
	                    "not problem constants, so they are read as nearest doubles)";
	if (!e.is_atom || e.is_string) throw ProtocolError(string(what) + PLAIN);
	if (e.atom == "+oo" || e.atom == "oo" || e.atom == "inf") return POS_INFINITY;
	if (e.atom == "-oo" || e.atom == "-inf") return NEG_INFINITY;
	NearestRounding nearest;
	const char* p = e.atom.c_str();
	char* end = NULL;
	double v = strtod(p, &end);
	if (end == p || *end != '\0')
		throw ProtocolError(string(what) + ": '" + e.atom + "' is not a number;" + PLAIN);
	return v;
}

long parse_int(const Sexp& e, const char* what) {
	if (!e.is_atom || e.is_string) throw ProtocolError(string(what) + " must be an integer");
	const char* p = e.atom.c_str();
	char* end = NULL;
	long v = strtol(p, &end, 10);
	if (end == p || *end != '\0')
		throw ProtocolError(string(what) + ": not an integer: '" + e.atom + "'");
	return v;
}

bool parse_bool(const Sexp& e, const char* what) {
	if (e.sym_is("true")) return true;
	if (e.sym_is("false")) return false;
	throw ProtocolError(string(what) + " must be true or false");
}

/*========================= expression building ==========================*/

/* Every node built here is registered and freed together when the solve ends.
 * SystemFactory copies whatever it is given (verified: the system still solves
 * after this set is released), so the solve owns its own DAG outright. */
class NodeSet {
public:
	~NodeSet() {
		if (nodes.empty()) return;
		Array<const ExprNode> roots(nodes.size());
		for (size_t i = 0; i < nodes.size(); i++) roots.set_ref(i, *nodes[i]);
		cleanup(roots, true);
	}

	const ExprNode& keep(const ExprNode& e) {
		nodes.push_back(&e); // cleanup() de-duplicates, so re-registering is safe
		return e;
	}

private:
	vector<const ExprNode*> nodes;
};

/* A definition is stored unevaluated. An Ibex expression is bound to particular
 * symbol objects, so it could not be reused across solves; a parameterised one
 * could not even be reused within a solve. Names in the body are resolved at the
 * point of USE, which is why a body mentioning a variable that has since been
 * popped fails there rather than at the point of definition. */
struct Definition {
	vector<string> params; // empty for a nullary define-fun
	Sexp body;
};

typedef map<string, Definition> DefineMap;

/* Names bound to already-built nodes: define-fun parameters, or one 'let'. */
typedef map<string, const ExprNode*> Frame;

/* Finished definition bodies. A body sees only its parameters and the globals, so
 * its name and argument nodes decide the result, and building it once per pair
 * keeps a ladder of definitions that mention each other twice from doubling. */
typedef map<pair<string, Frame>, const ExprNode*> ExpansionMap;

class Builder {
public:
	Builder(NodeSet& nodes, const map<string, const ExprSymbol*>& vars, const DefineMap& defs)
		: nodes(nodes), vars(vars), defs(defs), params(NULL) { }

	const ExprNode& build(const Sexp& e) {
		if (e.is_atom) return atom(e);
		if (e.list.empty()) throw ProtocolError("empty term '()'");
		if (!e.list[0].is_atom || e.list[0].is_string)
			throw ProtocolError("a term must start with a function name");
		const string& head = e.list[0].atom;
		if (head == "let") return let(e);
		if (head == "ite")
			throw ProtocolError("'ite' is a disjunction in disguise -- (ite c a b) holds when "
			                    "(c and a) or ((not c) and b) -- and is refused for the same "
			                    "reason 'or' is: Ibex searches a conjunction of constraints, so "
			                    "supporting it would mean weakening one branch silently. Assert "
			                    "the two cases separately with push/pop. For a branch on "
			                    "magnitude, 'min' and 'max' are supported and are what Ibex can "
			                    "actually contract");
		DefineMap::const_iterator d = defs.find(head);
		if (d != defs.end()) return call(d->first, d->second, e);
		return apply(head, e);
	}

private:
	NodeSet& nodes;
	const map<string, const ExprSymbol*>& vars;
	const DefineMap& defs;
	const Frame* params;  // parameters of the define-fun body being built, or NULL
	vector<Frame> lets;   // enclosing let scopes, innermost last
	vector<string> expanding;
	ExpansionMap expansions;

	/* Reports the whole chain, because "f is circular" alone does not say which
	 * hop to cut when the cycle runs through several definitions. */
	void check_not_circular(const string& name) {
		for (size_t i = 0; i < expanding.size(); i++) {
			if (expanding[i] != name) continue;
			string chain;
			for (size_t k = i; k < expanding.size(); k++) chain += expanding[k] + " -> ";
			throw ProtocolError("definition '" + name + "' is circular: " + chain + name);
		}
	}

	/* SMT-LIB let: every binding is built in the ENCLOSING scope and they take
	 * effect together, so (let ((x y) (y x)) ...) swaps rather than aliases. */
	const ExprNode& let(const Sexp& e) {
		if (e.list.size() != 3 || e.list[1].is_atom)
			throw ProtocolError("(let ((<name> <term>)...) <term>) expects a binding list and a body");
		Frame bound;
		const Sexp& bs = e.list[1];
		for (size_t k = 0; k < bs.list.size(); k++) {
			const Sexp& b = bs.list[k];
			if (b.is_atom || b.list.size() != 2 || !b.list[0].is_atom || b.list[0].is_string)
				throw ProtocolError("a let binding is (<name> <term>)");
			const string& n = b.list[0].atom;
			if (bound.count(n))
				throw ProtocolError("'" + n + "' is bound twice in the same let");
			bound[n] = &build(b.list[1]); // enclosing scope: 'bound' is not visible yet
		}
		lets.push_back(bound);
		try {
			const ExprNode& r = build(e.list[2]);
			lets.pop_back();
			return r;
		} catch (...) {
			lets.pop_back();
			throw;
		}
	}

	/* Builds a definition body with 'bound' as its parameters. Arguments have
	 * already been built in the CALLER's scope and are passed as nodes, so each
	 * argument is evaluated once however many times the body mentions it -- the
	 * shared node simply becomes a shared subexpression of the DAG. */
	const ExprNode& expand(const string& name, const Definition& def, const Frame& bound) {
		pair<string, Frame> key(name, bound);
		ExpansionMap::const_iterator done = expansions.find(key);
		if (done != expansions.end()) return *done->second;

		check_not_circular(name);
		expanding.push_back(name);
		const Frame* saved_params = params;
		vector<Frame> saved_lets;
		saved_lets.swap(lets); // a body never sees the caller's let bindings
		params = &bound;
		try {
			const ExprNode& r = build(def.body);
			params = saved_params;
			lets.swap(saved_lets);
			expanding.pop_back();
			expansions[key] = &r;
			return r;
		} catch (ProtocolError& e) {
			params = saved_params;
			lets.swap(saved_lets);
			expanding.pop_back();
			// The calling command often looks fine on its own; say where this came from.
			throw ProtocolError("in definition '" + name + "': " + e.msg);
		} catch (...) {
			params = saved_params;
			lets.swap(saved_lets);
			expanding.pop_back();
			throw;
		}
	}

	const ExprNode& call(const string& name, const Definition& def, const Sexp& e) {
		size_t nargs = e.list.size() - 1;
		if (def.params.empty())
			throw ProtocolError("'" + name + "' takes no arguments; write it as a bare name");
		if (nargs != def.params.size()) {
			ostringstream os;
			os << "'" << name << "' takes " << def.params.size()
			   << " argument" << (def.params.size() == 1 ? "" : "s") << ", got " << nargs;
			throw ProtocolError(os.str());
		}
		// Built here, in the caller's scope, before the frames are swapped.
		Frame bound;
		for (size_t k = 0; k < def.params.size(); k++)
			bound[def.params[k]] = &build(e.list[k + 1]);
		return expand(name, def, bound);
	}

	static bool is_unary(const string& op) {
		static const char* fns[] = { "sqrt", "exp", "log", "abs",
			"sin", "cos", "tan", "asin", "acos", "atan",
			"sinh", "cosh", "tanh", NULL };
		for (int i = 0; fns[i]; i++) if (op == fns[i]) return true;
		return false;
	}

	const ExprNode& atom(const Sexp& e) {
		if (e.is_string) throw ProtocolError("a string is not a term");
		const string& name = e.atom;
		if (looks_numeric(name))
			return nodes.keep(ExprConstant::new_scalar(parse_number_atom(name)));

		// Innermost binding wins: lets, then parameters, then globals.
		for (size_t k = lets.size(); k-- > 0; ) {
			Frame::const_iterator p = lets[k].find(name);
			if (p != lets[k].end()) return *p->second;
		}
		if (params) {
			Frame::const_iterator p = params->find(name);
			if (p != params->end()) return *p->second;
		}

		map<string, const ExprSymbol*>::const_iterator v = vars.find(name);
		if (v != vars.end()) return *v->second; // symbols are registered by the caller

		DefineMap::const_iterator d = defs.find(name);
		if (d == defs.end())
			throw ProtocolError("unknown name '" + name + "' (not a variable, parameter, "
			                    "binding, definition or number)");
		if (!d->second.params.empty()) {
			ostringstream os;
			os << "'" << name << "' takes " << d->second.params.size()
			   << " argument" << (d->second.params.size() == 1 ? "" : "s")
			   << "; it cannot be used as a bare name";
			throw ProtocolError(os.str());
		}
		return expand(name, d->second, Frame());
	}

	void want(const Sexp& e, size_t n, const string& op) {
		if (e.list.size() != n + 1) {
			ostringstream os;
			os << "'" << op << "' takes " << n << " argument" << (n == 1 ? "" : "s")
			   << ", got " << (e.list.size() - 1);
			throw ProtocolError(os.str());
		}
	}

	void want_at_least(const Sexp& e, size_t n, const string& op) {
		if (e.list.size() < n + 1) {
			ostringstream os;
			os << "'" << op << "' takes at least " << n << " arguments, got "
			   << (e.list.size() - 1);
			throw ProtocolError(os.str());
		}
	}

	const ExprNode& arg(const Sexp& e, size_t k) { return build(e.list[k]); }

	const ExprNode& apply(const string& op, const Sexp& e) {
		if (op == "+") {
			want_at_least(e, 1, op);
			const ExprNode* acc = &arg(e, 1);
			for (size_t k = 2; k < e.list.size(); k++) acc = &nodes.keep(*acc + arg(e, k));
			return *acc;
		}
		if (op == "*") {
			want_at_least(e, 1, op);
			const ExprNode* acc = &arg(e, 1);
			for (size_t k = 2; k < e.list.size(); k++) acc = &nodes.keep(*acc * arg(e, k));
			return *acc;
		}
		if (op == "-") {
			want_at_least(e, 1, op);
			if (e.list.size() == 2) return nodes.keep(-arg(e, 1));
			const ExprNode* acc = &arg(e, 1);
			for (size_t k = 2; k < e.list.size(); k++) acc = &nodes.keep(*acc - arg(e, k));
			return *acc;
		}
		if (op == "/") {
			want_at_least(e, 2, op);
			const ExprNode* acc = &arg(e, 1);
			for (size_t k = 2; k < e.list.size(); k++) acc = &nodes.keep(*acc / arg(e, k));
			return *acc;
		}

		if (op == "pow" || op == "^") {
			want(e, 2, op);
			// pow(expr,double) expands to exp(y*log(x)), which silently narrows the
			// domain to x>0, so only integer exponents are accepted. dReal takes a
			// real exponent here; that difference is deliberate and refused loudly
			// rather than answered on a smaller domain than the client wrote.
			if (!e.list[2].is_atom || e.list[2].is_string || !is_numeral(e.list[2].atom))
				throw ProtocolError("exponent of '" + op + "' must be an integer literal; "
				                    "a real exponent would restrict the base to x>0");
			long n = parse_int(e.list[2], "exponent");
			if (n < -1000 || n > 1000) throw ProtocolError("exponent of '" + op + "' out of range");
			const ExprNode& base = arg(e, 1);
			// Ibex's backward projection of x^0 takes a 0th root, which is empty, so
			// it would discard every box and read as a proof of unsat.
			if (n == 0) return nodes.keep(ExprConstant::new_scalar(Interval(1, 1)));
			return nodes.keep(pow(base, (int) n));
		}

		if (op == "atan2") { want(e, 2, op); return nodes.keep(atan2(arg(e, 1), arg(e, 2))); }
		if (op == "min" || op == "max") {
			want_at_least(e, 2, op);
			const ExprNode* acc = &arg(e, 1);
			for (size_t k = 2; k < e.list.size(); k++)
				acc = (op == "min") ? &nodes.keep(min(*acc, arg(e, k)))
				                    : &nodes.keep(max(*acc, arg(e, k)));
			return *acc;
		}

		// Identify before counting: otherwise (frobnicate a b) complains about the
		// argument count of a function that does not exist.
		if (!is_unary(op)) throw ProtocolError("unknown function '" + op + "'");
		want(e, 1, op);
		const ExprNode& a = arg(e, 1);
		if (op == "sqrt")  return nodes.keep(sqrt(a));
		if (op == "exp")   return nodes.keep(exp(a));
		if (op == "log")   return nodes.keep(log(a));
		if (op == "abs")   return nodes.keep(abs(a));
		if (op == "sin")   return nodes.keep(sin(a));
		if (op == "cos")   return nodes.keep(cos(a));
		if (op == "tan")   return nodes.keep(tan(a));
		if (op == "asin")  return nodes.keep(asin(a));
		if (op == "acos")  return nodes.keep(acos(a));
		if (op == "atan")  return nodes.keep(atan(a));
		if (op == "sinh")  return nodes.keep(sinh(a));
		if (op == "cosh")  return nodes.keep(cosh(a));
		if (op == "tanh")  return nodes.keep(tanh(a));
		throw ProtocolError("unknown function '" + op + "'");
	}
};

/*=============================== options ================================*/

struct Options {
	double rel_eps_f, abs_eps_f, eps_x, eps_h, timeout, random_seed;
	bool rigor, kkt;
	bool rigor_given, kkt_given;
	int trace, simpl_level;
	bool print_success;

	Options() { reset(); }

	void reset() {
		rel_eps_f = OptimizerConfig::default_rel_eps_f;
		abs_eps_f = OptimizerConfig::default_abs_eps_f;
		eps_x = OptimizerConfig::default_eps_x;
		eps_h = ExtendedSystem::default_eps_h;
		timeout = OptimizerConfig::default_timeout;
		random_seed = DefaultOptimizerConfig::default_random_seed;
		rigor = false; kkt = false;
		rigor_given = false; kkt_given = false;
		trace = OptimizerConfig::default_trace;
		simpl_level = ExprNode::default_simpl_level;
		print_success = false; // dReal's default, and what a pipe wants
	}
};

/*============================ solver state ==============================*/

/* One (push) level. Everything introduced inside it is undone by the matching
 * (pop), including the objective, which is why the old one is saved here. */
struct Scope {
	vector<string> vars;
	vector<string> defs;
	size_t n_asserts;
	Sexp objective;
	bool has_objective;
	bool maximize;
};

struct Objective {
	Sexp term;
	bool present;
	bool maximize;
	Objective() : present(false), maximize(false) { }
};

/* The result of the last (check-sat), kept for (get-objectives) / (get-model). */
struct LastResult {
	bool valid;          // a check-sat has run since the last change
	bool sat;
	bool has_bounds;
	double lo, hi;       // enclosure of the optimum, in the client's direction
	bool has_point;
	vector<string> names;
	IntervalVector point;
	LastResult() : valid(false), sat(false), has_bounds(false),
	               lo(0), hi(0), has_point(false), point(1) { }
};

struct State {
	vector<string> var_order;              // declaration order, for get-model
	map<string, bool> declared;            // name -> true (Real); the value is unused
	DefineMap defines;
	vector<Sexp> asserts;
	Objective objective;
	vector<Scope> scopes;
	Options options;
	LastResult last;
	bool logic_set;

	State() : logic_set(false) { }

	void reset_assertions() {
		asserts.clear();
		objective = Objective(); // part of the stack: (pop) restores it too
		scopes.clear();
		last.valid = false;
	}

	void reset() {
		var_order.clear();
		declared.clear();
		defines.clear();
		asserts.clear();
		objective = Objective();
		scopes.clear();
		options.reset();
		last = LastResult();
		logic_set = false;
	}

	bool is_taken(const string& n) const {
		return declared.count(n) != 0 || defines.count(n) != 0;
	}
};

State st;
bool want_exit = false;

/*========================= assertion analysis ===========================*/

/* A bound lifted out of an assertion and folded into a variable's domain. */
struct Bound {
	string var;
	double lo, hi;
};

bool is_declared_var(const string& n) {
	return st.declared.count(n) != 0;
}

/* True when the term is a literal this server can enclose without building
 * anything -- the right-hand side of a liftable bound. */
bool constant_term(const Sexp& e, Interval& v) {
	if (e.is_atom && !e.is_string && looks_numeric(e.atom)) {
		v = parse_number_atom(e.atom);
		return true;
	}
	// (- <literal>) is how a negative constant usually arrives.
	if (!e.is_atom && e.list.size() == 2 && e.list[0].sym_is("-")
	    && e.list[1].is_atom && !e.list[1].is_string && looks_numeric(e.list[1].atom)) {
		v = -parse_number_atom(e.list[1].atom);
		return true;
	}
	// (/ <literal> <literal>) is how an exact rational usually arrives.
	if (!e.is_atom && e.list.size() == 3 && e.list[0].sym_is("/")
	    && e.list[1].is_atom && !e.list[1].is_string && looks_numeric(e.list[1].atom)
	    && e.list[2].is_atom && !e.list[2].is_string && looks_numeric(e.list[2].atom)) {
		Interval d = parse_number_atom(e.list[2].atom);
		if (d.contains(0)) return false;
		v = parse_number_atom(e.list[1].atom) / d;
		return true;
	}
	return false;
}

bool bare_var(const Sexp& e, string& name) {
	if (!e.is_atom || e.is_string) return false;
	if (!is_declared_var(e.atom)) return false;
	name = e.atom;
	return true;
}

/* Recognises a two-term comparison that constrains one variable against one
 * constant, in either order. Bounds are taken OUTWARD so that the search box
 * encloses the asserted one. */
bool lift_pair(const string& op, const Sexp& a, const Sexp& b, Bound& out) {
	string name;
	Interval c;
	if (bare_var(a, name) && constant_term(b, c)) {
		// name OP c
		if (op == "<=" || op == "<") { out.var = name; out.lo = NEG_INFINITY; out.hi = c.ub(); return true; }
		if (op == ">=" || op == ">") { out.var = name; out.lo = c.lb(); out.hi = POS_INFINITY; return true; }
		if (op == "=")               { out.var = name; out.lo = c.lb(); out.hi = c.ub(); return true; }
		return false;
	}
	if (bare_var(b, name) && constant_term(a, c)) {
		// c OP name
		if (op == "<=" || op == "<") { out.var = name; out.lo = c.lb(); out.hi = POS_INFINITY; return true; }
		if (op == ">=" || op == ">") { out.var = name; out.lo = NEG_INFINITY; out.hi = c.ub(); return true; }
		if (op == "=")               { out.var = name; out.lo = c.lb(); out.hi = c.ub(); return true; }
		return false;
	}
	return false;
}

bool is_comparison(const string& op) {
	return op == "<=" || op == "<" || op == ">=" || op == ">" || op == "=";
}

/* Negates a comparison. Strict and non-strict swap, which is exact over the
 * reals -- unlike the relaxation that happens when a strict bound is lifted. */
string negate_comparison(const string& op) {
	if (op == "<=") return ">";
	if (op == "<")  return ">=";
	if (op == ">=") return "<";
	if (op == ">")  return "<=";
	return ""; // (not (= a b)) has no single-constraint form
}

void validate_term(const Sexp& e); // defined below; used to check comparison operands

struct Flat {
	vector<Bound> bounds;                 // folded into variable domains
	vector<pair<string, pair<Sexp, Sexp> > > ctrs; // op, lhs, rhs
	bool trivially_false;
	Flat() : trivially_false(false) { }
};

void flatten(const Sexp& e, Flat& out, bool negated);

void flatten_comparison(const string& op0, const Sexp& e, Flat& out, bool negated) {
	string op = op0;
	if (negated) {
		// (not (< a b c)) is (a >= b) or (b >= c): negating each link would turn
		// that disjunction into a much stronger conjunction.
		if (e.list.size() > 3)
			throw ProtocolError("a negated chain of '" + op0 + "' is a disjunction; assert the "
			                    "cases separately (push/pop)");
		op = negate_comparison(op0);
		if (op.empty())
			throw ProtocolError("(not (= ...)) is a disequality, which cannot be expressed "
			                    "as a single constraint; assert < or > instead");
	}
	for (size_t k = 1; k < e.list.size(); k++) validate_term(e.list[k]);
	// SMT-LIB comparisons are chained: (< a b c) means a<b and b<c.
	for (size_t k = 1; k + 1 < e.list.size(); k++) {
		Bound b;
		bool lifted = lift_pair(op, e.list[k], e.list[k+1], b);
		if (lifted) out.bounds.push_back(b);
		// A box endpoint cannot exclude itself, so a strict bound also stays a constraint.
		if (!lifted || op == "<" || op == ">")
			out.ctrs.push_back(make_pair(op, make_pair(e.list[k], e.list[k+1])));
	}
}

/* Splits a formula into bounds and constraints. Only conjunctions survive:
 * Ibex's SystemFactory takes a conjunction of constraints and nothing else, so a
 * disjunction is refused rather than silently weakened into one. */
void flatten(const Sexp& e, Flat& out, bool negated) {
	if (e.is_atom) {
		if (e.sym_is("true"))  { if (negated) out.trivially_false = true; return; }
		if (e.sym_is("false")) { if (!negated) out.trivially_false = true; return; }
		throw ProtocolError("'" + e.atom + "' is not a formula");
	}
	if (e.list.empty() || !e.list[0].is_atom || e.list[0].is_string)
		throw ProtocolError("a formula must start with a connective or comparison");

	const string& head = e.list[0].atom;

	if (head == "not") {
		if (e.list.size() != 2) throw ProtocolError("(not <formula>) takes one argument");
		flatten(e.list[1], out, !negated);
		return;
	}
	if (head == "and" && !negated) {
		for (size_t k = 1; k < e.list.size(); k++) flatten(e.list[k], out, false);
		return;
	}
	if (head == "or" && negated) { // de Morgan: (not (or a b)) is (and (not a) (not b))
		for (size_t k = 1; k < e.list.size(); k++) flatten(e.list[k], out, true);
		return;
	}
	if (head == "or" || head == "and" || head == "xor" || head == "=>" || head == "implies") {
		throw ProtocolError("'" + head + "' would make the assertion a disjunction; Ibex "
		                    "searches a conjunction of constraints, so assert the cases "
		                    "separately (push/pop) rather than have this weakened silently");
	}
	if (head == "let")
		throw ProtocolError("'let' at formula level is not supported; put it inside a "
		                    "comparison's terms instead");
	if (is_comparison(head)) {
		if (e.list.size() < 3)
			throw ProtocolError("'" + head + "' takes at least two terms");
		flatten_comparison(head, e, out, negated);
		return;
	}
	throw ProtocolError("'" + head + "' is not a formula");
}

/*=========================== term validation ============================*/

/* Arity of the builtin functions: {min args, max args}, 0 meaning unbounded. */
struct Arity { const char* name; size_t lo; size_t hi; };

const Arity ARITIES[] = {
	{ "+", 1, 0 }, { "*", 1, 0 }, { "-", 1, 0 }, { "/", 2, 0 },
	{ "min", 2, 0 }, { "max", 2, 0 },
	{ "pow", 2, 2 }, { "^", 2, 2 }, { "atan2", 2, 2 },
	{ "sqrt", 1, 1 }, { "exp", 1, 1 }, { "log", 1, 1 }, { "abs", 1, 1 },
	{ "sin", 1, 1 }, { "cos", 1, 1 }, { "tan", 1, 1 },
	{ "asin", 1, 1 }, { "acos", 1, 1 }, { "atan", 1, 1 },
	{ "sinh", 1, 1 }, { "cosh", 1, 1 }, { "tanh", 1, 1 },
	{ NULL, 0, 0 }
};

/* Structural check of a term, run where the term is ACCEPTED rather than where
 * it is solved. 'assert' already gets this from flatten(); without it an
 * objective would sit unexamined until a check-sat several commands later, and
 * a client that replaced the objective in between would never see the error at
 * all. Name resolution is deliberately left to the build, because a let binding
 * is only visible there. */
void validate_term(const Sexp& e) {
	if (e.is_atom) {
		if (e.is_string) throw ProtocolError("a string is not a term");
		if (looks_numeric(e.atom)) parse_number_atom(e.atom); // enclosable?
		return;
	}
	if (e.list.empty()) throw ProtocolError("empty term '()'");
	if (!e.list[0].is_atom || e.list[0].is_string)
		throw ProtocolError("a term must start with a function name");

	const string& head = e.list[0].atom;
	size_t nargs = e.list.size() - 1;

	if (head == "let") {
		if (e.list.size() != 3 || e.list[1].is_atom)
			throw ProtocolError("(let ((<name> <term>)...) <term>) expects a binding list and a body");
		const Sexp& bs = e.list[1];
		for (size_t k = 0; k < bs.list.size(); k++) {
			const Sexp& b = bs.list[k];
			if (b.is_atom || b.list.size() != 2 || !b.list[0].is_atom || b.list[0].is_string)
				throw ProtocolError("a let binding is (<name> <term>)");
			validate_term(b.list[1]);
		}
		validate_term(e.list[2]);
		return;
	}

	if (head == "ite")
		throw ProtocolError("'ite' is a disjunction in disguise -- (ite c a b) holds when "
		                    "(c and a) or ((not c) and b) -- and is refused for the same reason "
		                    "'or' is: Ibex searches a conjunction of constraints, so supporting "
		                    "it would mean weakening one branch silently. Assert the two cases "
		                    "separately with push/pop. For a branch on magnitude, 'min' and "
		                    "'max' are supported and are what Ibex can actually contract");
	if (head == "and" || head == "or" || head == "not" || head == "xor"
	 || head == "=>" || head == "implies" || is_comparison(head))
		throw ProtocolError("'" + head + "' is a formula, not a term; it cannot be the value "
		                    "of an objective or an argument to a function");

	for (int i = 0; ARITIES[i].name; i++) {
		if (head != ARITIES[i].name) continue;
		if (nargs < ARITIES[i].lo || (ARITIES[i].hi && nargs > ARITIES[i].hi)) {
			ostringstream os;
			os << "'" << head << "' takes ";
			if (ARITIES[i].hi == ARITIES[i].lo) os << ARITIES[i].lo << " argument"
			                                       << (ARITIES[i].lo == 1 ? "" : "s");
			else os << "at least " << ARITIES[i].lo << " arguments";
			os << ", got " << nargs;
			throw ProtocolError(os.str());
		}
		if (head == "pow" || head == "^") {
			// Checked here as well as in the build so that the reason arrives with
			// the command that wrote it.
			if (!e.list[2].is_atom || e.list[2].is_string || !is_numeral(e.list[2].atom))
				throw ProtocolError("exponent of '" + head + "' must be an integer literal; "
				                    "a real exponent would restrict the base to x>0");
		}
		for (size_t k = 1; k < e.list.size(); k++) validate_term(e.list[k]);
		return;
	}

	// Not a builtin: it must be a define-fun, and it must exist by now -- SMT-LIB
	// requires a name to be declared before it is used.
	DefineMap::const_iterator d = st.defines.find(head);
	if (d == st.defines.end())
		throw ProtocolError("unknown function '" + head + "'");
	if (nargs != d->second.params.size()) {
		ostringstream os;
		os << "'" << head << "' takes " << d->second.params.size()
		   << " argument" << (d->second.params.size() == 1 ? "" : "s") << ", got " << nargs;
		throw ProtocolError(os.str());
	}
	for (size_t k = 1; k < e.list.size(); k++) validate_term(e.list[k]);
}

/*================================ solve =================================*/

CmpOp cmp_of(const string& op) {
	if (op == "<=") return LEQ;
	if (op == "<")  return LT;
	if (op == ">=") return GEQ;
	if (op == ">")  return GT;
	return EQ;
}

/* Ibex's Optimizer needs a goal. With no objective the question is pure
 * feasibility, so a constant is minimized and only the status is read. */
string do_check_sat() {
	st.last = LastResult();

	Flat flat;
	for (size_t i = 0; i < st.asserts.size(); i++) flatten(st.asserts[i], flat, false);

	if (flat.trivially_false) {
		st.last.valid = true;
		st.last.sat = false;
		return "unsat";
	}

	if (st.var_order.empty())
		throw ProtocolError("nothing to solve: no variable has been declared");

	// Domains start unbounded and are tightened by every lifted bound.
	map<string, Interval> domain;
	for (size_t i = 0; i < st.var_order.size(); i++)
		domain[st.var_order[i]] = Interval(NEG_INFINITY, POS_INFINITY);
	for (size_t i = 0; i < flat.bounds.size(); i++) {
		Interval& d = domain[flat.bounds[i].var];
		double lo = d.lb() > flat.bounds[i].lo ? d.lb() : flat.bounds[i].lo;
		double hi = d.ub() < flat.bounds[i].hi ? d.ub() : flat.bounds[i].hi;
		if (lo > hi) { // the asserted bounds contradict each other outright
			st.last.valid = true;
			st.last.sat = false;
			return "unsat";
		}
		d = Interval(lo, hi);
	}

	NodeSet nodes; // declared first so it outlives everything built from it
	map<string, const ExprSymbol*> vars;
	SystemFactory fac;
	fac.set_simplification_level(st.options.simpl_level);

	// Ibex fatally rejects a variable added after the goal or a constraint
	// (SystemFactory::add_var), so every variable goes in first.
	for (size_t i = 0; i < st.var_order.size(); i++) {
		const string& name = st.var_order[i];
		const ExprSymbol& sym = ExprSymbol::new_(name.c_str());
		nodes.keep(sym);
		vars[name] = &sym;
		fac.add_var(sym, domain[name]);
	}

	Builder builder(nodes, vars, st.defines);

	bool maximize = st.objective.present && st.objective.maximize;
	if (st.objective.present) {
		const ExprNode& goal = builder.build(st.objective.term);
		// Ibex only minimizes (Optimizer reports "loup", the lowest upper bound of
		// the criterion), so max f is solved as min -f and the bounds are negated
		// and swapped on the way out.
		fac.add_goal(maximize ? nodes.keep(-goal) : goal);
	} else {
		fac.add_goal(nodes.keep(ExprConstant::new_scalar(Interval(0, 0))));
	}

	for (size_t k = 0; k < flat.ctrs.size(); k++) {
		const ExprNode& lhs = builder.build(flat.ctrs[k].second.first);
		const ExprNode& rhs = builder.build(flat.ctrs[k].second.second);
		// Built by hand rather than via operator<=, which heap-allocates an
		// ExprCtr that nothing ever frees.
		ExprCtr ctr(nodes.keep(lhs - rhs), cmp_of(flat.ctrs[k].first));
		fac.add_ctr(ctr);
	}

	System sys(fac);

	DefaultOptimizerConfig config(sys);
	config.set_eps_h(st.options.eps_h);
	if (st.options.rigor_given) config.set_rigor(st.options.rigor);
	if (st.options.kkt_given) config.set_kkt(st.options.kkt);
	config.set_random_seed(st.options.random_seed);
	config.set_rel_eps_f(st.options.rel_eps_f);
	config.set_abs_eps_f(st.options.abs_eps_f);
	config.set_eps_x(Vector(sys.nb_var, st.options.eps_x));
	config.set_timeout(st.options.timeout);
	config.set_trace(st.options.trace);

	Optimizer o(config);
	Optimizer::Status status = o.optimize(sys.box);

	st.last.valid = true;
	st.last.names = st.var_order;

	if (status == Optimizer::INFEASIBLE) {
		st.last.sat = false;
		return "unsat";
	}

	double uplo = o.get_uplo(), loup = o.get_loup();
	st.last.has_bounds = st.objective.present;
	st.last.lo = maximize ? -loup : uplo;
	st.last.hi = maximize ? -uplo : loup;

	bool found = (loup != POS_INFINITY) && !o.get_loup_point().is_empty();
	if (found) {
		st.last.has_point = true;
		st.last.point = o.get_loup_point();
	}

	// UNBOUNDED_OBJ only means some box has no finite lower bound on the objective,
	// which says nothing about feasibility, so "sat" still needs a point.
	st.last.sat = found && (status == Optimizer::SUCCESS || status == Optimizer::UNBOUNDED_OBJ);
	return st.last.sat ? "sat" : "unknown";
}

string do_get_objectives() {
	if (!st.last.valid) throw ProtocolError("no (check-sat) has been run");
	if (!st.objective.present) throw ProtocolError("no objective has been set");
	if (!st.last.has_bounds) throw ProtocolError("the last (check-sat) produced no bounds");
	string kind = st.objective.maximize ? "maximize" : "minimize";
	return "(objectives (" + kind + " " + fmt(st.last.lo) + " " + fmt(st.last.hi) + "))";
}

/* The model carries one value per variable and SMT-LIB has no interval value
 * form, so a box cannot go here. In rigor mode Ibex certifies a box rather than
 * a point; its midpoint stands in, and the certified bounds are served by
 * (get-info :ibex-enclosure). Outside rigor mode the box is degenerate and the
 * midpoint is the point itself. */
string value_of(const Interval& c) {
	return smt_real(c.mid());
}

/* One ULP outward before printing. The shortest round-tripping decimal recovers
 * the double it was made from, but its exact rational value is not that double:
 * 1.4142135623730951 read exactly is 14142135623730951/10^16, a different
 * number, and it can fall inside the certified box. A reader doing exact
 * arithmetic would then hold a box Ibex never proved. Stepping the bound one ULP
 * outward first puts the printed decimal strictly outside, since it lands within
 * half an ULP of a value already a full ULP clear. The box widens by two ULPs
 * and stays sound, which is the right way round for this trade. */
string enclosure_bound(double v, bool upward) {
	double w = nextafter(v, upward ? POS_INFINITY : NEG_INFINITY);
	if (w == POS_INFINITY || w == NEG_INFINITY) w = v; // v was +-DBL_MAX
	if (w != w || w == POS_INFINITY || w == NEG_INFINITY)
		throw ProtocolError("the enclosure has an unbounded component");
	return smt_real(w);
}

/* Reported whenever a point exists, not only after "sat". A timeout answers
 * unknown but can still have found a feasible point, and (get-objectives)
 * already reports the bound THAT POINT certifies -- refusing to show the point
 * itself would hide the witness for exactly the runs where it is most wanted.
 * After "unsat" there is no point by construction. */
string do_get_model() {
	if (!st.last.valid) throw ProtocolError("no (check-sat) has been run");
	if (!st.last.has_point)
		throw ProtocolError(st.last.sat ? "no point was found"
		                                : "no point was found (the last (check-sat) answered "
		                                  "unsat or found nothing)");
	string out = "(";
	for (size_t i = 0; i < st.last.names.size(); i++) {
		if (i) out += " ";
		out += "(define-fun " + smt_symbol(st.last.names[i]) + " () Real "
		     + value_of(st.last.point[(int) i]) + ")";
	}
	return out + ")";
}

string do_get_value(const Sexp& req) {
	if (req.list.size() != 2 || req.list[1].is_atom)
		throw ProtocolError("(get-value (<term>...)) takes a list of terms");
	if (!st.last.valid) throw ProtocolError("no (check-sat) has been run");
	if (!st.last.has_point) throw ProtocolError("no point was found");

	const Sexp& terms = req.list[1];
	string out = "(";
	for (size_t k = 0; k < terms.list.size(); k++) {
		const Sexp& t = terms.list[k];
		if (!t.is_atom || t.is_string)
			throw ProtocolError("(get-value ...) reports declared variables; "
			                    "compound terms are not evaluated here");
		int idx = -1;
		for (size_t i = 0; i < st.last.names.size(); i++)
			if (st.last.names[i] == t.atom) { idx = (int) i; break; }
		if (idx < 0) throw ProtocolError("'" + t.atom + "' is not a declared variable");
		if (k) out += " ";
		out += "(" + smt_symbol(t.atom) + " " + value_of(st.last.point[idx]) + ")";
	}
	return out + ")";
}

/* Where the box goes. SMT-LIB reserves :keyword for exactly this and says an
 * unrecognised one answers "unsupported", so the channel costs a conforming
 * client nothing: the reply is an ordinary s-expression whether or not the
 * client knows the keyword, and a client that does not ask never sees it.
 *
 * Reported whenever a point exists, on the same terms as (get-model). Outside
 * rigor mode every component is degenerate and the reply repeats the model to
 * within the two ULPs of outward rounding; it is worth asking for only under
 * :ibex-rigor true, where the bounds are what Ibex actually certified. */
string do_get_info(const Sexp& req) {
	if (req.list.size() != 2 || !req.list[1].is_atom || req.list[1].is_string)
		throw ProtocolError("(get-info :<key>) expects a keyword");
	if (req.list[1].atom != ":ibex-enclosure") throw Unsupported();

	if (!st.last.valid) throw ProtocolError("no (check-sat) has been run");
	if (!st.last.has_point)
		throw ProtocolError(st.last.sat ? "no point was found"
		                                : "no point was found (the last (check-sat) answered "
		                                  "unsat or found nothing)");
	string out = "(:ibex-enclosure (";
	for (size_t i = 0; i < st.last.names.size(); i++) {
		const Interval& c = st.last.point[(int) i];
		if (i) out += " ";
		out += "(" + smt_symbol(st.last.names[i]) + " " + enclosure_bound(c.lb(), false)
		     + " " + enclosure_bound(c.ub(), true) + ")";
	}
	return out + "))";
}

/*============================== commands ================================*/

/* Names that would either be shadowed into uselessness (the builtin wins and
 * the definition is silently dead) or would shadow a keyword a reader will
 * misread. Refused outright rather than resolved by precedence. */
bool is_reserved(const string& n) {
	static const char* words[] = {
		// commands
		"set-logic", "set-option", "set-info", "declare-fun", "declare-const",
		"define-fun", "assert", "minimize", "maximize", "check-sat", "get-model",
		"get-value", "get-objectives", "push", "pop", "reset", "reset-assertions",
		"echo", "exit",
		// sorts and literals
		"Real", "Int", "Bool", "true", "false",
		// connectives, comparisons and binders
		"and", "or", "not", "xor", "=>", "implies", "ite", "let", "forall", "exists",
		"=", "<", "<=", ">", ">=",
		// functions
		"+", "-", "*", "/", "pow", "^", "sqrt", "exp", "log", "abs", "min", "max",
		"sin", "cos", "tan", "asin", "acos", "atan", "atan2",
		"sinh", "cosh", "tanh",
		NULL };
	for (int i = 0; words[i]; i++) if (n == words[i]) return true;
	return false;
}

void check_name(const Sexp& e, const char* what, string& out) {
	if (!e.is_atom || e.is_string || e.atom.empty() || looks_numeric(e.atom))
		throw ProtocolError(string(what) + " must be a symbol");
	out = e.atom;
}

/* Only DECLARED names are checked against the reserved list. A parameter is
 * only ever looked up as a bare atom, while functions are only ever matched as
 * list heads -- so (define-fun f ((exp Real)) Real (exp)) is a name clash the
 * client can have, and (exp x) inside that body still means the function. */
void check_definable(const Sexp& e, const char* what, string& out) {
	check_name(e, what, out);
	if (is_reserved(out))
		throw ProtocolError(string(what) + " '" + out + "' is reserved");
	if (st.is_taken(out))
		throw ProtocolError("'" + out + "' is already declared; pop a scope to reuse the name");
}

void want_sort_real(const Sexp& e, const string& who) {
	if (e.sym_is("Real")) return;
	if (e.sym_is("Int"))
		throw ProtocolError("'" + who + "': sort Int is not supported -- Ibex has no "
		                    "integrality constraint here, so accepting it would answer a "
		                    "different problem; declare it Real and assert its bounds");
	if (e.sym_is("Bool"))
		throw ProtocolError("'" + who + "': sort Bool is not supported; this server "
		                    "solves over the reals");
	throw ProtocolError("'" + who + "': unknown sort (only Real is supported)");
}

void declare_var(const string& name) {
	st.declared[name] = true;
	st.var_order.push_back(name);
	if (!st.scopes.empty()) st.scopes.back().vars.push_back(name);
	st.last.valid = false;
}

void run_declare_const(const Sexp& req) {
	if (req.list.size() != 3) throw ProtocolError("(declare-const <name> Real)");
	string name;
	check_definable(req.list[1], "a declared name", name);
	want_sort_real(req.list[2], name);
	declare_var(name);
}

void run_declare_fun(const Sexp& req) {
	if (req.list.size() != 4 || req.list[2].is_atom)
		throw ProtocolError("(declare-fun <name> () Real)");
	string name;
	check_definable(req.list[1], "a declared name", name);
	if (!req.list[2].list.empty())
		throw ProtocolError("'" + name + "': uninterpreted functions are not supported; "
		                    "only (declare-fun " + name + " () Real)");
	want_sort_real(req.list[3], name);
	declare_var(name);
}

void run_define_fun(const Sexp& req) {
	if (req.list.size() != 5 || req.list[2].is_atom)
		throw ProtocolError("(define-fun <name> ((<param> Real)...) Real <term>)");
	string name;
	check_definable(req.list[1], "a defined name", name);

	Definition def;
	const Sexp& ps = req.list[2];
	for (size_t k = 0; k < ps.list.size(); k++) {
		const Sexp& p = ps.list[k];
		if (p.is_atom || p.list.size() != 2)
			throw ProtocolError("a parameter of '" + name + "' is (<name> Real)");
		string pn;
		check_name(p.list[0], "a parameter name", pn);
		want_sort_real(p.list[1], pn);
		for (size_t j = 0; j < def.params.size(); j++)
			if (def.params[j] == pn)
				throw ProtocolError("parameter '" + pn + "' of '" + name + "' is repeated");
		def.params.push_back(pn);
	}
	want_sort_real(req.list[3], name);

	def.body = req.list[4];
	st.defines[name] = def;
	if (!st.scopes.empty()) st.scopes.back().defs.push_back(name);
	st.last.valid = false;
}

void run_assert(const Sexp& req) {
	if (req.list.size() != 2) throw ProtocolError("(assert <formula>) takes one formula");
	// Parsed now so a malformed assertion is reported at the assert rather than
	// several commands later at the check-sat.
	Flat probe;
	flatten(req.list[1], probe, false);
	st.asserts.push_back(req.list[1]);
	st.last.valid = false;
}

void run_objective(const Sexp& req, bool maximize) {
	const char* who = maximize ? "maximize" : "minimize";
	if (req.list.size() != 2)
		throw ProtocolError(string("(") + who + " <term>) takes one term");
	validate_term(req.list[1]);
	st.objective.term = req.list[1];
	st.objective.present = true;
	st.objective.maximize = maximize;
	st.last.valid = false;
}

void run_set_option(const Sexp& req) {
	if (req.list.size() != 3 || !req.list[1].is_atom || req.list[1].is_string)
		throw ProtocolError("(set-option :<key> <value>) expects a keyword and a value");
	const string& key = req.list[1].atom;
	const Sexp& v = req.list[2];
	Options& o = st.options;

	if (key == ":print-success") { o.print_success = parse_bool(v, key.c_str()); return; }

	if (key == ":precision") {
		// dReal's delta. It bounds how far a reported solution may be from
		// satisfying the constraints, which is what eps-h does here; eps-x is set
		// with it so the box search stops at a comparable scale.
		double d = parse_plain_double(v, ":precision");
		if (!(d > 0)) throw ProtocolError(":precision must be > 0");
		o.eps_h = d;
		o.eps_x = d;
		return;
	}

	if (key == ":ibex-rel-eps-f" || key == ":ibex-abs-eps-f"
	 || key == ":ibex-eps-x" || key == ":ibex-eps-h") {
		double d = parse_plain_double(v, key.c_str());
		if (!(d >= 0)) throw ProtocolError(key + " must be >= 0");
		if (key == ":ibex-rel-eps-f") o.rel_eps_f = d;
		else if (key == ":ibex-abs-eps-f") o.abs_eps_f = d;
		else if (key == ":ibex-eps-x") o.eps_x = d;
		else o.eps_h = d;
		return;
	}
	if (key == ":ibex-timeout")     { o.timeout = parse_plain_double(v, key.c_str()); return; }
	if (key == ":ibex-random-seed") { o.random_seed = parse_plain_double(v, key.c_str()); return; }
	if (key == ":ibex-rigor") { o.rigor = parse_bool(v, key.c_str()); o.rigor_given = true; return; }
	if (key == ":ibex-kkt")   { o.kkt = parse_bool(v, key.c_str()); o.kkt_given = true; return; }
	if (key == ":ibex-trace") {
		long t = parse_int(v, key.c_str());
		if (t < 0 || t > 2) throw ProtocolError(":ibex-trace must be 0, 1 or 2");
		o.trace = (int) t;
		return;
	}
	if (key == ":ibex-simpl-level") {
		long l = parse_int(v, key.c_str());
		if (l < 0 || l > 3) throw ProtocolError(":ibex-simpl-level must be 0..3");
		o.simpl_level = (int) l;
		return;
	}
	// SMT-LIB says an unknown option is not an error; the standard reply is
	// "unsupported", so a client can set solver-specific options blind.
	throw Unsupported();
}

string do_get_option(const Sexp& req) {
	if (req.list.size() != 2 || !req.list[1].is_atom || req.list[1].is_string)
		throw ProtocolError("(get-option :<key>) expects a keyword");
	const string& key = req.list[1].atom;
	const Options& o = st.options;
	if (key == ":print-success")    return o.print_success ? "true" : "false";
	if (key == ":precision")        return fmt(o.eps_h);
	if (key == ":ibex-rel-eps-f")   return fmt(o.rel_eps_f);
	if (key == ":ibex-abs-eps-f")   return fmt(o.abs_eps_f);
	if (key == ":ibex-eps-x")       return fmt(o.eps_x);
	if (key == ":ibex-eps-h")       return fmt(o.eps_h);
	if (key == ":ibex-timeout")     return fmt(o.timeout);
	if (key == ":ibex-random-seed") return fmt(o.random_seed);
	if (key == ":ibex-rigor")       return o.rigor ? "true" : "false";
	if (key == ":ibex-kkt")         return o.kkt ? "true" : "false";
	{
		ostringstream os;
		if (key == ":ibex-trace")       { os << o.trace; return os.str(); }
		if (key == ":ibex-simpl-level") { os << o.simpl_level; return os.str(); }
	}
	throw Unsupported();
}

void run_set_logic(const Sexp& req) {
	if (req.list.size() != 2 || !req.list[1].is_atom || req.list[1].is_string)
		throw ProtocolError("(set-logic <name>) expects a logic name");
	const string& l = req.list[1].atom;
	// The arithmetic logics are accepted; Int is refused later, at the
	// declaration that actually needs it, where the message can be useful.
	if (l.find("RA") == string::npos && l.find("IA") == string::npos)
		throw ProtocolError("logic '" + l + "' is not supported; this server solves "
		                    "QF_NRA (nonlinear real arithmetic)");
	st.logic_set = true;
}

long scope_count(const Sexp& req, const char* who) {
	if (req.list.size() == 1) return 1;
	if (req.list.size() != 2) throw ProtocolError(string("(") + who + " [<n>]) takes at most one argument");
	long n = parse_int(req.list[1], who);
	if (n < 0) throw ProtocolError(string(who) + " count must be >= 0");
	return n;
}

void run_push(const Sexp& req) {
	long n = scope_count(req, "push");
	for (long k = 0; k < n; k++) {
		Scope s;
		s.n_asserts = st.asserts.size();
		s.objective = st.objective.term;
		s.has_objective = st.objective.present;
		s.maximize = st.objective.maximize;
		st.scopes.push_back(s);
	}
}

void run_pop(const Sexp& req) {
	long n = scope_count(req, "pop");
	if ((size_t) n > st.scopes.size())
		throw ProtocolError("(pop) with no matching (push)");
	for (long k = 0; k < n; k++) {
		Scope& s = st.scopes.back();
		for (size_t i = 0; i < s.vars.size(); i++) {
			st.declared.erase(s.vars[i]);
			for (size_t j = 0; j < st.var_order.size(); j++)
				if (st.var_order[j] == s.vars[i]) { st.var_order.erase(st.var_order.begin() + j); break; }
		}
		for (size_t i = 0; i < s.defs.size(); i++) st.defines.erase(s.defs[i]);
		st.asserts.resize(s.n_asserts);
		st.objective.term = s.objective;
		st.objective.present = s.has_objective;
		st.objective.maximize = s.maximize;
		st.scopes.pop_back();
	}
	st.last.valid = false;
}

/* SMT-LIB quotes a string with "..." and doubles any embedded quote. */
string quote(const string& s) {
	string out = "\"";
	for (size_t i = 0; i < s.size(); i++) {
		if (s[i] == '"') out += '"';
		out += s[i];
	}
	return out + "\"";
}

/* Returns the reply, or "" for a command that succeeded silently. */
string dispatch(const Sexp& req) {
	if (req.is_atom) throw ProtocolError("a command must be a list");
	if (req.list.empty()) throw ProtocolError("empty command '()'");
	if (!req.list[0].is_atom || req.list[0].is_string)
		throw ProtocolError("a command must start with a command name");

	const string& head = req.list[0].atom;
	const char* SUCCESS = "success";

	if (head == "check-sat") {
		if (req.list.size() != 1) throw ProtocolError("(check-sat) takes no argument");
		return do_check_sat();
	}
	if (head == "get-objectives") {
		if (req.list.size() != 1) throw ProtocolError("(get-objectives) takes no argument");
		return do_get_objectives();
	}
	if (head == "get-model") {
		if (req.list.size() != 1) throw ProtocolError("(get-model) takes no argument");
		return do_get_model();
	}
	if (head == "get-value")  return do_get_value(req);
	if (head == "get-option") return do_get_option(req);
	if (head == "get-info")   return do_get_info(req);

	if (head == "echo") {
		if (req.list.size() != 2 || !req.list[1].is_string)
			throw ProtocolError("(echo \"<string>\") takes one string");
		return quote(req.list[1].atom);
	}
	if (head == "exit") {
		if (req.list.size() != 1) throw ProtocolError("(exit) takes no argument");
		want_exit = true;
		return st.options.print_success ? SUCCESS : "";
	}

	if (head == "set-logic")      run_set_logic(req);
	else if (head == "set-option") run_set_option(req);
	else if (head == "set-info") {
		if (req.list.size() < 2 || req.list.size() > 3)
			throw ProtocolError("(set-info :<key> [<value>]) expects a keyword and an optional value");
		// Metadata; recorded by nothing and refused by nothing.
	}
	else if (head == "declare-const") run_declare_const(req);
	else if (head == "declare-fun")   run_declare_fun(req);
	else if (head == "define-fun")    run_define_fun(req);
	else if (head == "assert")        run_assert(req);
	else if (head == "minimize")      run_objective(req, false);
	else if (head == "maximize")      run_objective(req, true);
	else if (head == "push")          run_push(req);
	else if (head == "pop")           run_pop(req);
	else if (head == "reset-assertions") st.reset_assertions();
	else if (head == "reset")            st.reset();
	else if (head == "declare-sort" || head == "define-sort" || head == "define-fun-rec"
	      || head == "check-sat-assuming" || head == "get-assertions"
	      || head == "get-assignment" || head == "get-proof"
	      || head == "get-unsat-core" || head == "get-unsat-assumptions")
		throw Unsupported();
	else
		throw ProtocolError("unknown command '" + head + "'");

	return st.options.print_success ? SUCCESS : "";
}

/* Never throws: every failure becomes a reply. */
string handle(const Sexp& req) {
	try {
		return dispatch(req);
	}
	catch (Unsupported&) {
		return "unsupported";
	}
	catch (ProtocolError& e) {
		return "(error " + quote(e.msg) + ")";
	}
	catch (SyntaxError& e) {
		return "(error " + quote("ibex: " + e.msg) + ")";
	}
	catch (ibex::Exception& e) {
		return "(error " + quote(string("ibex: ") + e.what()) + ")";
	}
	catch (std::exception& e) {
		return "(error " + quote(string("ibex: ") + e.what()) + ")";
	}
	catch (...) {
		return "(error \"ibex: unknown failure\")";
	}
}

/*========================== files and watching ==========================*/

/* Ibex-side messages go to stderr; fd 1 belongs to the protocol. */
void warn(const string& msg) {
	fprintf(stderr, "ibexquery: %s\n", msg.c_str());
}

string where(const string& path) {
	if (!path.empty() && path[0] == '/') return "";
	char cwd[PATH_MAX];
	if (!getcwd(cwd, sizeof(cwd))) return "";
	return string(" (searched in ") + cwd + ")";
}

/* Returns false and sets 'err' saying why. stat() succeeding proves nothing
 * about readability, so the file is actually opened. */
bool slurp(const string& path, string& text, string& err) {
	struct stat sb;
	if (stat(path.c_str(), &sb) != 0) {
		err = "cannot read '" + path + "': " + strerror(errno) + where(path);
		return false;
	}
	if (S_ISDIR(sb.st_mode)) {
		err = "cannot read '" + path + "': is a directory" + where(path);
		return false;
	}

	int fd = open(path.c_str(), O_RDONLY);
	if (fd < 0) {
		err = "cannot read '" + path + "': " + strerror(errno) + where(path);
		return false;
	}

	text.clear();
	char buf[65536];
	for (;;) {
		ssize_t n = read(fd, buf, sizeof(buf));
		if (n < 0) {
			if (errno == EINTR) continue;
			err = "cannot read '" + path + "': " + strerror(errno) + where(path);
			close(fd);
			return false;
		}
		if (n == 0) break;
		text.append(buf, (size_t) n);
	}
	close(fd);
	return true;
}

void emit(const string& line) {
	if (!line.empty()) reply(line);
}

void run_text(const string& text) {
	vector<Sexp> forms;
	string err;
	FormStatus st_ = scan_all(text, forms, err);

	for (size_t i = 0; i < forms.size(); i++) {
		emit(handle(forms[i]));
		if (want_exit) return;
	}
	if (st_ == FORM_INCOMPLETE) reply("(error \"unterminated expression at end of input\")");
	else if (st_ == FORM_ERROR) reply("(error " + quote(err) + ")");
}

double now_seconds() {
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (double) ts.tv_sec + 1e-9 * (double) ts.tv_nsec;
}

void nap(double seconds) {
	struct timespec ts;
	ts.tv_sec = (time_t) seconds;
	ts.tv_nsec = (long) ((seconds - (double) ts.tv_sec) * 1e9);
	nanosleep(&ts, NULL);
}

/* Identity, not just mtime: an editor's atomic save swaps in a new inode and
 * the size may well be unchanged. */
struct FileId {
	dev_t dev; ino_t ino; off_t size; time_t mtime; long mtime_ns;
	bool valid;
	FileId() : dev(0), ino(0), size(0), mtime(0), mtime_ns(0), valid(false) { }
	bool operator!=(const FileId& o) const {
		return valid != o.valid || dev != o.dev || ino != o.ino
		    || size != o.size || mtime != o.mtime || mtime_ns != o.mtime_ns;
	}
};

FileId stat_id(const string& path) {
	FileId id;
	struct stat sb;
	if (stat(path.c_str(), &sb) != 0) return id;
	id.dev = sb.st_dev; id.ino = sb.st_ino; id.size = sb.st_size;
	id.mtime = sb.st_mtime;
#ifdef __APPLE__
	id.mtime_ns = sb.st_mtimespec.tv_nsec;
#else
	id.mtime_ns = sb.st_mtim.tv_nsec;
#endif
	id.valid = true;
	return id;
}

/* How often to look for a change; set by --interval. */
double watch_poll = 0.2;

/* The inner wait for a writer to finish is a different thing from the outer
 * change poll, so it keeps its own short period: a long --interval must not eat
 * the whole give-up window before the file has been re-read even once. */
const double WATCH_RECHECK = 0.02;
const double WATCH_GIVE_UP = 2.0;

/* Waits for the file to hold complete balanced forms rather than for a fixed
 * settle delay -- a settle delay is only ever a bet on the writer being quick.
 * A file that never parses is run anyway after WATCH_GIVE_UP so that a real
 * syntax error still reaches the client. */
bool read_when_complete(const string& path, string& text, FileId& id) {
	double deadline = now_seconds() + WATCH_GIVE_UP;
	for (;;) {
		FileId cur = stat_id(path);
		string err;
		if (cur.valid && slurp(path, text, err)) {
			id = cur;
			vector<Sexp> forms;
			string perr;
			if (scan_all(text, forms, perr) != FORM_INCOMPLETE) return true;
			if (now_seconds() >= deadline) return true; // let the error surface
		} else if (now_seconds() >= deadline) {
			if (!err.empty()) warn(err);
			return false;
		}
		nap(WATCH_RECHECK);
	}
}

/* One pass of a watched file. The whole solver state is reset first so that a
 * declaration deleted from the file is really gone, rather than surviving from
 * the previous run and making the file look like it still works. */
void watch_run(const string& text) {
	st.reset();
	run_text(text);
	if (want_exit) {
		// A stray (exit) ends this pass only: it must not silently kill the
		// watcher the client is relying on.
		warn("(exit) ends this pass; still watching");
		want_exit = false;
	}
}

int watch_file(const string& path) {
	string text, err;
	FileId id = stat_id(path); // before the read, so a save during it counts as a change
	if (!slurp(path, text, err)) {
		warn(err);
		return 1;
	}
	watch_run(text);

	for (;;) {
		nap(watch_poll);
		FileId cur = stat_id(path);
		if (!cur.valid || !(cur != id)) continue; // gone mid-rename, or unchanged
		if (read_when_complete(path, text, id)) watch_run(text);
	}
}

int run_stdin() {
	string buf;
	char chunk[65536];

	for (;;) {
		// Drain whatever complete forms the buffer already holds.
		for (;;) {
			Sexp form;
			string err;
			FormStatus fs;
			size_t consumed;
			{
				Reader r(buf); // holds a reference to buf: done before the erase
				fs = r.next(form, err);
				consumed = r.offset();
			}
			if (fs == FORM_EOF || fs == FORM_INCOMPLETE) break;
			buf.erase(0, consumed);
			if (fs == FORM_ERROR) reply("(error " + quote(err) + ")");
			else {
				emit(handle(form));
				if (want_exit) return 0;
			}
		}

		ssize_t n = read(STDIN_FILENO, chunk, sizeof(chunk));
		if (n < 0) {
			if (errno == EINTR) continue;
			warn(string("cannot read stdin: ") + strerror(errno));
			return 1;
		}
		if (n == 0) { // EOF
			Reader r(buf);
			Sexp form;
			string err;
			if (r.next(form, err) == FORM_INCOMPLETE)
				reply("(error \"unterminated expression at end of input\")");
			return 0;
		}
		buf.append(chunk, (size_t) n);
	}
}

} // anonymous namespace

int main(int argc, char** argv) {

#ifdef __IBEX_NO_LP_SOLVER__
	ibex_error("ibexquery requires a LP Solver (use -DLP_LIB with cmake)");
	exit(1);
#endif

	// Before anything else: keep the protocol stream clean whatever the library
	// decides to print.
	reply_fd = dup(STDOUT_FILENO);
	if (reply_fd < 0 || dup2(STDERR_FILENO, STDOUT_FILENO) < 0) {
		fprintf(stderr, "ibexquery: cannot redirect stdout: %s\n", strerror(errno));
		return 1;
	}

	args::ArgumentParser parser("********* IbexQuery (persistent SMT-LIB optimizer server) *********.",
			"Reads SMT-LIB 2 commands (dReal dialect) from stdin, or from the given files.");
	args::HelpFlag help(parser, "help", "Display this help menu", {'h', "help"});
	args::Flag version(parser, "version", "Display the version of this plugin (same as the version of Ibex).", {'v', "version"});
	args::Flag watch(parser, "watch", "Re-run the given file each time it changes.", {'w', "watch"});
	args::ValueFlag<long> interval(parser, "ms", "How often --watch polls for changes, in "
			"milliseconds. Default value is 200.", {"interval"});
	args::PositionalList<string> files(parser, "filename", "Command files, run in order; '-' means "
			"stdin. Without any, commands are read from stdin.", {});

	try {
		parser.ParseCLI(argc, argv);
	}
	catch (args::Help&) {
		cerr << parser;
		return 0;
	}
	catch (args::ParseError& e) {
		cerr << e.what() << endl << parser;
		return 1;
	}
	catch (args::ValidationError& e) {
		cerr << e.what() << endl << parser;
		return 1;
	}

	if (version) {
		reply(string("IbexQuery Release ") + _IBEX_RELEASE_);
		return 0;
	}

	vector<string> paths = args::get(files);

	if (interval) {
		if (interval.Get() < 1) {
			warn("--interval must be at least 1 ms");
			return 1;
		}
		watch_poll = (double) interval.Get() / 1000.0;
	}

	if (watch) {
		if (paths.size() != 1) {
			warn("--watch takes exactly one file");
			return 1;
		}
		if (paths[0] == "-") {
			warn("--watch needs a file; stdin cannot be watched for changes");
			return 1;
		}
		return watch_file(paths[0]);
	}

	if (paths.empty()) return run_stdin();

	for (size_t i = 0; i < paths.size(); i++) {
		if (paths[i] == "-") {
			int rc = run_stdin();
			if (rc != 0) return rc;
		} else {
			string text, err;
			if (!slurp(paths[i], text, err)) {
				warn(err);
				return 1; // unreadable input is a failure, not an empty run
			}
			run_text(text);
		}
		// Reading files, (exit) stops here and skips whatever is left.
		if (want_exit) break;
	}
	return 0;
}
