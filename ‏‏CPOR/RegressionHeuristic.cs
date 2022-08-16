using System;
using System.Collections.Generic;

namespace CPOR
{
    class RegressionHeuristic : HeuristicFunction
    {
        private Domain m_dDomain;
        private List<Predicate> m_lGoal;
        private bool m_bMax;
        List<SortedSet<Predicate>> m_lRegressionLayers;
        Dictionary<Predicate, int> m_dFirstRegressionLayer;

        public RegressionHeuristic(Domain d, Formula fGoal, bool bMax)
        {
            m_dDomain = d;
            m_bMax = bMax;
            m_lGoal = new List<Predicate>(fGoal.GetAllPredicates());
            //ComputeFullRegression();
        }
        /*
        private void ComputeFullRegression()
        {

            //useless - doesn't work
            m_lRegressionLayers = new List<SortedSet<Predicate>>();
            m_dFirstRegressionLayer = new Dictionary<Predicate, int>();

            m_lRegressionLayers.Add(new SortedSet<Predicate>(m_lGoal));
            foreach (Predicate p in m_lGoal)
                m_dFirstRegressionLayer[p] = 0;

            bool bChanged = true;
            SortedSet<Predicate> lAllAchievable = new SortedSet<Predicate>( m_lRegressionLayers.Last());
            List<GroundedPredicate> lAllPredicates = m_dDomain.GroundAllPredicates();
            List<Action> lActions = m_dDomain.GroundAllActions(lAllPredicates, true); //bugbug - need to check that it works
            int cExpansions = 0;
            while (bChanged)
            {
                cExpansions++;
                SortedSet<Predicate> lNewLayer = new SortedSet<Predicate>();

                bChanged = false;
                foreach (Action a in lActions)
                {
                    if (a.Effects != null)
                    {
                        foreach (Predicate p in lAllAchievable)
                        {
                            List<Predicate> lPreconditionsForAchievingEffect = a.PreconditionsForEffect(p);
                            foreach (Predicate pTag in lPreconditionsForAchievingEffect)
                            {
                                if (!lAllAchievable.Contains(pTag))
                                {
                                    lNewLayer.Add(pTag);
                                    m_dFirstRegressionLayer[pTag] = m_lRegressionLayers.Count;
                                    bChanged = true;
                                }
                            }
                        }
                    }
                }
                m_lRegressionLayers.Add(lNewLayer);
                foreach (Predicate p in lNewLayer)
                    lAllAchievable.Add(p);
            }           
        }
        */
        private double Delta(State s)
        {
            Dictionary<Predicate, int> dCostForAchieving = new Dictionary<Predicate, int>();
            foreach (Predicate p in s.Predicates)
            {
                dCostForAchieving[p] = 0;
            }
            bool bChanged = true;
            //State sVirtual = s.Clone();
            SortedSet<Predicate> lAllAchevablePredicates = new SortedSet<Predicate>(s.Predicates);
            int cExpansions = 0;
            while (bChanged)
            {
                cExpansions++;
                List<Predicate> lCurrentPredicates = new List<Predicate>(lAllAchevablePredicates);
                List<Action> lActions = m_dDomain.GroundAllActions(lCurrentPredicates, true);
                bChanged = false;
                foreach (Action a in lActions)
                {
                    if (a.Effects != null)
                    {
                        int cMaxCostForPrecondition = 0;
                        int cSumPreconditionsCosts = 0;
                        bool bApplicable = true;
                        if (a.Preconditions != null)
                        {
                            HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                            foreach (Predicate p in lPreconditions)
                            {
                                if (dCostForAchieving.ContainsKey(p))
                                {
                                    if (dCostForAchieving[p] > cMaxCostForPrecondition)
                                        cMaxCostForPrecondition = dCostForAchieving[p];
                                    cSumPreconditionsCosts += dCostForAchieving[p];
                                }
                                else
                                {
                                    bApplicable = false;
                                }
                            }
                        }
                        if (bApplicable)
                        {
                            HashSet<Predicate> lEffects = a.GetApplicableEffects(lCurrentPredicates, true).GetAllPredicates();
                            foreach (Predicate p in lEffects)
                            {
                                //if (!p.Negation)
                                {
                                    if (!dCostForAchieving.ContainsKey(p))
                                    {
                                        if (m_bMax)
                                            dCostForAchieving[p] = cMaxCostForPrecondition + 1;
                                        else
                                            dCostForAchieving[p] = cSumPreconditionsCosts + 1;
                                        lAllAchevablePredicates.Add(p);
                                        bChanged = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            int iMaxCost = 0, cSumCosts = 0;
            foreach (Predicate p in m_lGoal)
            {
                if (!dCostForAchieving.ContainsKey(p))
                    return Double.PositiveInfinity;
                else
                {
                    if (dCostForAchieving[p] > iMaxCost)
                    {
                        iMaxCost = dCostForAchieving[p];
                    }
                    cSumCosts += dCostForAchieving[p];
                }
            }
            if (m_bMax)
                return iMaxCost;
            else
                return cSumCosts;
        }

        public override double h(State s)
        {
            return Delta(s);
        }



        public override Dictionary<State, Action> GetNextStates(State s)
        {
            throw new NotImplementedException();
        }
    }
}
