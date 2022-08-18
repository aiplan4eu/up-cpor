using System;
using System.Collections.Generic;
using System.Diagnostics;
using Action = CPORLib.PlanningModel.PlanningAction;
using CPORLib.PlanningModel;
using CPORLib.LogicalUtilities;

namespace CPORLib.Algorithms
{
    class HSPHeuristic : HeuristicFunction
    {
        private Dictionary<Predicate, int> m_dComputedCosts;
        private Domain m_dDomain;
        private List<Predicate> m_lGoal;
        private bool m_bMax;
        private Dictionary<Predicate, List<SortedSet<Predicate>>> m_dParents;
        private List<Action> m_lGroundedActions;

        public HSPHeuristic(Domain d, Formula fGoal, bool bMax)
        {
            m_dDomain = d;
            m_bMax = bMax;
            m_lGoal = new List<Predicate>(fGoal.GetAllPredicates());
            m_lGroundedActions = null;
        }

        public HSPHeuristic(List<Action> lActions, Formula fGoal, bool bMax)
        {
            m_dDomain = null;
            m_lGroundedActions = lActions;
            m_bMax = bMax;
            m_lGoal = new List<Predicate>(fGoal.GetAllPredicates());
        }

        private void ComputeAllEffectsPreconditions()
        {
            HashSet<GroundedPredicate> lAllPositivePredicates = m_dDomain.GroundAllPredicates();
            HashSet<Predicate> lAllPredicates = new HashSet<Predicate>();
            foreach (Predicate p in lAllPositivePredicates)
            {
                lAllPredicates.Add(p);
                lAllPredicates.Add(p.Negate());
            }
            List<Action> lAllActions = m_lGroundedActions;
            if (lAllActions == null)
                lAllActions = m_dDomain.GroundAllActions();
            m_dParents = new Dictionary<Predicate, List<SortedSet<Predicate>>>();
            foreach (Predicate p in lAllPredicates)
            {
                if (!m_dDomain.AlwaysConstant(p))
                {
                    m_dParents[p] = new List<SortedSet<Predicate>>();
                    foreach (Action a in lAllActions)
                    {
                        List<HashSet<Predicate>> lAllPossiblePreconditions = a.PreconditionsForEffect(p);
                        if (lAllPossiblePreconditions != null)
                        {
                            foreach (HashSet<Predicate> lPreconditions in lAllPossiblePreconditions)
                            {
                                SortedSet<Predicate> s = new SortedSet<Predicate>();
                                foreach (Predicate pTag in lPreconditions)
                                {
                                    if (!m_dDomain.AlwaysConstant(pTag))
                                        s.Add(pTag);
                                }
                                m_dParents[p].Add(s);
                            }
                        }
                    }
                }
            }
        }

        private double DeltaII(State s)
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


        private double Delta(State s, List<Action> lPlan)
        {
            Dictionary<Predicate, HashSet<Predicate>> dEffectToPreconditions = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, Action> dParentAction = new Dictionary<Predicate, Action>();
            foreach (Predicate p in s.Predicates)
            {
                dParentAction[p] = null;
            }
            bool bChanged = true;
            //State sVirtual = s.Clone();
            HashSet<Predicate> lAllAcheavablePredicates = new HashSet<Predicate>(s.Predicates);
            int cExpansions = 0;
            List<HashSet<Action>> lExpansions = new List<HashSet<Action>>();
            HashSet<Action> lAllObservedActions = new HashSet<Action>();
            while (bChanged)
            {
                lExpansions.Add(new HashSet<Action>());
                HashSet<Predicate> lCurrentPredicates = new HashSet<Predicate>(lAllAcheavablePredicates);
                //List<Action> lActions = m_dDomain.GroundAllActions(lCurrentPredicates, true);
                bChanged = false;
                foreach (Action a in m_lGroundedActions)
                {

                    //if (a.Name.Contains("feel") & a.Name.Contains("3-5"))
                    //    Console.Write("*");
                    if (a.Preconditions.IsTrue(lCurrentPredicates, false))
                    {
                        if (cExpansions == 0 || !lAllObservedActions.Contains(a))
                        {
                            lExpansions[cExpansions].Add(a);
                            lAllObservedActions.Add(a);
                        }
                        if (a.Effects != null)
                        {
                            Dictionary<Predicate, Formula> dCurrentEffectToPreconditions = new Dictionary<Predicate, Formula>();
                            SortedSet<Predicate> lEffects = a.GetApplicableEffects(lCurrentPredicates, true, dCurrentEffectToPreconditions);
                            bool bNewAction = false;
                            foreach (Predicate p in lEffects)
                            {
                                if (!lAllAcheavablePredicates.Contains(p))
                                {
                                    bNewAction = true;
                                    dParentAction[p] = a;
                                    if (dCurrentEffectToPreconditions[p] != null)
                                        dEffectToPreconditions[p] = dCurrentEffectToPreconditions[p].GetAllPredicates();
                                    else
                                        dEffectToPreconditions[p] = null;
                                    lAllAcheavablePredicates.Add(p);
                                    bChanged = true;
                                }
                            }
                            //if (bNewAction)
                            //    Debug.WriteLine(a.Name);
                        }
                    }
                }
                cExpansions++;
            }
            int cActions = 0;
            List<Predicate> lNeedToAchievePredicates = new List<Predicate>(m_lGoal);
            List<Predicate> lAchieved = new List<Predicate>();
            while (lNeedToAchievePredicates.Count > 0)
            {
                List<Action> lActions = new List<Action>();
                SortedSet<Predicate> lPreconditions = new SortedSet<Predicate>();
                foreach (Predicate p in lNeedToAchievePredicates)
                {
                    if (dParentAction.ContainsKey(p))
                    {
                        if (!lActions.Contains(dParentAction[p]) && dParentAction[p] != null)
                        {
                            lActions.Add(dParentAction[p]);
                            lPlan.Add(dParentAction[p]);
                        }
                        if (dParentAction[p] != null)
                        {
                            if (dEffectToPreconditions[p] != null)
                            {
                                foreach (Predicate pTag in dEffectToPreconditions[p])
                                {
                                    if (!lAchieved.Contains(pTag))
                                        lPreconditions.Add(pTag);
                                }
                            }
                        }
                        lAchieved.Add(p);
                    }
                    else if (m_lGoal.Contains(p))
                        return double.PositiveInfinity;
                }
                cActions += lActions.Count;
                lNeedToAchievePredicates = new List<Predicate>(lPreconditions);
            }
            lPlan.Reverse();

            if (cActions == 0)
                Debug.WriteLine("BUGBUG");
            return cActions;
        }

        private int CostForAchieving(Predicate p, State s, Dictionary<Predicate, int> dCostForAchieving, List<Predicate> lObserved)
        {
            if (s.Contains(p))
                return 0;
            if (dCostForAchieving.ContainsKey(p))
                return dCostForAchieving[p];
            if (lObserved.Contains(p))
                return int.MaxValue;
            lObserved.Add(p);
            int iMin = int.MaxValue - 1;
            foreach (SortedSet<Predicate> sParents in m_dParents[p])
            {
                int iMax = 0;
                int iSum = 0;
                foreach (Predicate pTag in sParents)
                {
                    int iCostForPTag = CostForAchieving(pTag, s, dCostForAchieving, lObserved);
                    if (iCostForPTag == int.MaxValue)
                    {
                        iSum = int.MaxValue - 1;
                        break;
                    }
                    iSum += iCostForPTag;
                    if (iCostForPTag > iMax)
                        iMax = iCostForPTag;
                }
                //if (iMax < iMin)
                //    iMin = iMax;
                if (iSum < iMin)
                    iMin = iSum;
            }

            lObserved.Remove(p);

            //if (iMin < 0)
            //     Debug.WriteLine("*");

            dCostForAchieving[p] = iMin + 1;
            return iMin + 1;
        }

        private double DeltaI(State s)
        {
            Dictionary<Predicate, int> dCostForAchieving = new Dictionary<Predicate, int>();
            int iMaxCost = 0, cSumCosts = 0;
            HashSet<GroundedPredicate> lPredicates = m_dDomain.GroundAllPredicates();
            List<Action> lActions = m_dDomain.GroundAllActions(lPredicates, true);
            List<Predicate> lObserved = new List<Predicate>();
            foreach (Predicate p in m_lGoal)
            {
                int iCost = CostForAchieving(p, s, dCostForAchieving, lObserved);
                cSumCosts += iCost;
                if (iCost > iMaxCost)
                    iMaxCost = iCost;
            }

            if (m_bMax)
                return iMaxCost;
            else
                return cSumCosts;
        }

        public override double h(State s)
        {
            return Delta(s, new List<Action>());
        }
        /*
        public override Dictionary<State, Action> GetNextStates(State s)
        {
            List<Action> lPlan = new List<Action>();
            double cActions = Delta(s, lPlan);
            Dictionary<State, Action> lStates = new Dictionary<State, Action>();
            foreach (Action a in lPlan)
            {
                State sTag = s.Apply(a);
                if (sTag != null)
                    lStates[sTag] = a;
            }
            return lStates;
        }
        */
        public override Dictionary<State, Action> GetNextStates(State s)
        {
            Dictionary<State, Action> lStates = new Dictionary<State, Action>();
            foreach (Action a in m_lGroundedActions)
            {
                State sNext = s.Apply(a);
                if (sNext != null)
                {
                    lStates[sNext] = a;
                    //BUGBUG;//likely it does not identify the correct state in the parents dictionary, probably due to the change in equals
                    //if (a.Name.Contains("4-5") || a.Name.Contains("5-4"))
                    //    Console.Write("*");
                }
            }
            return lStates;
        }
    }
}
