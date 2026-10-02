//============================================================================
//                                  I B E X
// File        : ibex_LoupFinderCertify.h
// Author      : Gilles Chabert
// Copyright   : IMT Atlantique (France)
// License     : See the LICENSE file
// Created     : Jul 20, 2017
//============================================================================

#ifndef __IBEX_LOUP_FINDER_CERTIFY_H__
#define __IBEX_LOUP_FINDER_CERTIFY_H__

#include "ibex_LoupFinder.h"
#include "ibex_Exception.h"
#include "ibex_NormalizedSystem.h"

#include <utility>

namespace ibex {

/**
 * \ingroup optim
 *
 * \brief Certify a loup point.
 *
 * This finder works like a post-processing: it first runs an unsafe
 * finder working on relaxed equalities. The "pseudo" loup found
 * is then made rigorous by running a Newton-inflation algorithm.
 *
 * This results in a box that rigorously includes a feasible
 * point.
 */
class LoupFinderCertify : public LoupFinder {
public:

	/**
	 * \param sys    - The real system (that is, without relaxation).
	 * \param finder - A loup finder for the relaxed system.
	 * \param eps_h  - Initial threshold for an inequality to be considered
	 *                 as active. Should match the equality thickness used
	 *                 to relax the system. A feasible region thinner than
	 *                 this threshold makes both sides of a two-sided
	 *                 constraint look active at once, so the threshold is
	 *                 lowered on the fly when the proof fails (see
	 *                 #max_activity_trials).
	 */
	LoupFinderCertify(const System& sys, LoupFinder& finder,
			double eps_h=NormalizedSystem::default_eps_h);

	/**
	 * \brief Find a new loup in a given box.
	 *
	 * \see comments in LoupFinder.
	 */
	virtual std::pair<IntervalVector, double> find(const IntervalVector& box, const IntervalVector& loup_point, double loup) override;

	/**
	 * \brief Return true.
	 */
	virtual bool rigorous() const override {
		return true;
	}

	/**
	 * Minimal threshold for an inequality
	 * to be considered as active.
	 */
	const double min_activity_thershold = 1e-20;

	/**
	 * Maximal number of times the activity threshold is halved after a
	 * failed feasibility proof. Each retry costs one Hansen test, so this
	 * bounds the extra work spent on a box that cannot be certified.
	 */
	const int max_activity_trials = 10;

protected:

	/**
	 * \brief The NLP problem.
	 */
	const System& sys;

	/**
	 * \brief Initial activity detection threshold.
	 */
	const double eps_h;

	/**
	 * \brief True iff there is an equality.
	 */
	const bool has_equality;

	/**
	 * \brief Finder for the relaxed system.
	 */
	LoupFinder& finder;
};

} /* namespace ibex */

#endif /* __IBEX_LOUP_FINDER_CERTIFY_H__ */
