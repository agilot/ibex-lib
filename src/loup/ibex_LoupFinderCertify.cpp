//============================================================================
//                                  I B E X
// File        : ibex_LoupFinderCertify.cpp
// Author      : Gilles Chabert
// Copyright   : IMT Atlantique (France)
// License     : See the LICENSE file
// Created     : Jul 20, 2017
//============================================================================

#include "ibex_PdcHansenFeasibility.h"
#include "ibex_FncActiveCtrs.h"
#include "ibex_LoupFinderCertify.h"
#include "ibex_NormalizedSystem.h"

namespace ibex {

using namespace std;

LoupFinderCertify::LoupFinderCertify(const System& sys, LoupFinder& finder, double eps_h) : sys(sys), eps_h(eps_h), has_equality(false), finder(finder) {

	if (sys.nb_ctr>0)
		// ==== check if the system contains equalities ====
		for (int i=0; i<sys.f_ctrs.image_dim(); i++) {
			if (sys.ops[i]==EQ) {
				(bool&) has_equality = true;
				break;
			}
		}
}

//pair<IntervalVector, double> LoupCorrection::find(double loup, const Vector& loup_point, double pseudo_loup) {
std::pair<IntervalVector, double> LoupFinderCertify::find(const IntervalVector& box, const IntervalVector& loup_point, double loup) {

	IntervalVector epsbox(box.size());
	bool pseudo_loup_found=true;
	pair<IntervalVector,double> p;

	try {
		p=finder.find(box,loup_point,loup);
		epsbox = p.first;
	} catch(NotFound&) {
		pseudo_loup_found=false;
		epsbox=box.mid();
	}

	if (pseudo_loup_found && !has_equality)
		return p;

	// The activity threshold decides which inequalities are treated as tight
	// when assembling the square system the Hansen test works on. A single
	// threshold is not enough, because two distinct situations defeat it and
	// both are cured by lowering it:
	//
	//  - too many active constraints: the system is overconstrained and no
	//    proof is possible at all (this was the only case handled before);
	//
	//  - a feasible region thinner than the threshold: both sides of a
	//    two-sided constraint (-eps <= g(x) <= eps with eps below the
	//    threshold) are seen as tight at once, so the square system demands
	//    g(x)==-eps and g(x)==+eps simultaneously. That is unsatisfiable, so
	//    Newton inflation returns MAYBE forever while the active set stays
	//    small enough to look perfectly well-posed.
	//
	// So we retry with progressively more selective active sets instead of
	// giving up after a single attempt. max_activity_trials bounds the extra
	// Hansen tests spent on a box that simply cannot be certified.

	double threshold = eps_h;
	bool overconstrained = false;

	// The first attempt always runs: eps_h may legitimately start at or below the minimum.
	for (int trial=0; trial<=max_activity_trials && (trial==0 || threshold>min_activity_thershold);
			trial++, threshold/=2.) {

		FncActiveCtrs* af;

		try {
			af = new FncActiveCtrs(sys,epsbox.lb(),threshold,false);
		} catch(FncActiveCtrs::NothingActive&) {
			if (pseudo_loup_found)
				return p;
			else
				throw NotFound();
		}

		// we cannot make proofs with overconstrained systems
		if (af->image_dim() > sys.nb_var) {
			delete af;
			overconstrained = true;
			continue;
		}
		overconstrained = false;

		// ====================================================
		// solution #1: we inflate the loup-point and
		//              call Hansen test in contracting mode.
		//	epsbox.inflate(NormalizedSystem::default_eps_h);
		//	PdcHansenFeasibility pdc(af, false);
		// ====================================================

		// ====================================================
		// solution #2: we call Hansen test in inflating mode.
		PdcHansenFeasibility pdc(*af, true);
		// ====================================================

		// TODO: maybe we should check first if the epsbox is inner...
		// otherwise the probability to get a feasible point is
		// perhaps too small?

		// TODO: HansenFeasibility uses midpoint
		//       but maybe we should use random

		if (pdc.test(epsbox)!=YES) {
			// the proof failed: a more selective active set may still succeed.
			delete af;
			continue;
		}

		// The proof succeeded. Whether or not the certified point turns out
		// to be usable, a smaller threshold would not change that, so this
		// is the last iteration either way.
		Interval resI = sys.goal->eval(pdc.solution());
		if (!resI.is_empty()) {
			double res=resI.ub();
			if (res<loup) {
				//note: don't call is_inner because it would check again all equalities (which is useless
				// and perhaps wrong as the solution box may violate the relaxed inequality (still, very unlikely))
				bool satisfy_inequalities=true;

				// we must check the inequalities that are not active (for
				// the latters, feasibility is already OK).
				// It is unlikely that they are violated but still possible.
				if (!sys.box.intersects(pdc.solution()))
					satisfy_inequalities=false;
				else if (sys.nb_ctr>0) {
					for (int j=0; j<sys.f_ctrs.image_dim(); j++) {
						if (!af->active_ctr[j])
							if (((sys.ops[j]==LEQ || sys.ops[j]==LT)
									&& sys.f_ctrs.eval(j,pdc.solution()).ub()>0)
									||
									((sys.ops[j]==GEQ || sys.ops[j]==GT)
											&& sys.f_ctrs.eval(j,pdc.solution()).lb()<0)) {


								satisfy_inequalities=false;
								break;
							}
					}
				}
				if (satisfy_inequalities) {
					delete af;
					return make_pair(pdc.solution(), res);
				}
			}
		}

		delete af;
		throw NotFound();
	}

	//===========================================================
	if (overconstrained)
		ibex_warning("too many active constraints, cannot prove feasibility -> loup lost!");

	throw NotFound();
}

} /* namespace ibex */
