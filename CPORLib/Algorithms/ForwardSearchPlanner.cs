using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Action = CPORLib.PlanningModel.PlanningAction;

namespace CPORLib.Algorithms
{
    class ForwardSearchPlanner : Planner
    {
        private HeuristicFunction m_fHeuristic;
        private int m_cObservedStates;
        private List<Action> m_lGroundedActions;

        public ForwardSearchPlanner(Domain d, Problem p, HeuristicFunction fHeuristic)
            : base(d, p)
        {
            m_fHeuristic = fHeuristic;
        }

        public ForwardSearchPlanner(MemoryStream msModel)
            : base(null, null)
        {
            Parser p = new Parser();
            msModel.Position = 0;
            p.ParseDomainAndProblem(msModel, out m_dDomain, out m_pProblem);

            /*
            Console.WriteLine(m_dDomain);
            Console.WriteLine("************");
            Console.WriteLine(m_pProblem);
            Console.WriteLine("************");
            */



            m_lGroundedActions = m_dDomain.GroundAllActions(m_pProblem, true);

            //m_fHeuristic = new HSPHeuristic(m_dDomain, m_pProblem.Goal, true);
            m_fHeuristic = new HSPHeuristic(m_lGroundedActions, m_pProblem.Goal, true);
        }

        public List<Action> PlanII(State sStartState)
        {
            CompoundFormula fGoal = (CompoundFormula)m_pProblem.Goal;
            //List<Predicate> lGoal = new List<Predicate>();
            //foreach (PredicateFormula vf in fGoal.Operands)
            //    lGoal.Add(vf.Predicate);
            State sCurrent = null, sNext = null;
            List<State> lOpenList = new List<State>();
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            Dictionary<State, Action> dGeneratingAction = new Dictionary<State, Action>();
            Dictionary<State, double> dHeuristic = new Dictionary<State, double>();
            Dictionary<State, double> dCost = new Dictionary<State, double>();
            int cRepeated = 0;
            dCost[sStartState] = 0;
            dHeuristic[sStartState] = m_fHeuristic.h(sStartState);
            lOpenList.Add(sStartState);
            dParents[sStartState] = null;
            dGeneratingAction[sStartState] = null;
            m_cObservedStates = 1;
            int cHandled = 0;
            while (lOpenList.Count > 0)
            {
                sCurrent = GetMinimalStateBFS(lOpenList, dHeuristic, dCost);
                cHandled++;
                Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + cHandled + ", " + dHeuristic[sCurrent] + "," + lOpenList.Count);
                lOpenList.Remove(sCurrent);
                foreach (Action a in m_lGroundedActions)
                {
                    sNext = sCurrent.Apply(a);
                    if (sNext != null && !dParents.ContainsKey(sNext))
                    {
                        m_cObservedStates++;
                        dParents[sNext] = sCurrent;
                        dGeneratingAction[sNext] = a;
                        if (sNext.Contains(fGoal))
                            return CreatePlan(sNext, dParents, dGeneratingAction);
                        else
                        {
                            dCost[sNext] = dCost[sCurrent] + 1;
                            dHeuristic[sNext] = m_fHeuristic.h(sNext);
                            lOpenList.Add(sNext);
                        }
                    }
                    else if (sNext != null)
                        cRepeated++;
                }
            }
            return null;
        }
        public List<Action> Plan()
        {
            State sStartState = m_pProblem.GetInitialBelief().ChooseState(true);
            return Plan(sStartState);
        }
        public override List<Action> Plan(State sStartState)
        {
            Formula fGoal = m_pProblem.Goal;
            //List<Predicate> lGoal = new List<Predicate>();
            //foreach (PredicateFormula vf in fGoal.Operands)
            //    lGoal.Add(vf.Predicate);
            State sCurrent = null;
            List<State> lOpenList = new List<State>();
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            Dictionary<State, Action> dGeneratingAction = new Dictionary<State, Action>();
            Dictionary<State, double> dHeuristic = new Dictionary<State, double>();
            Dictionary<State, double> dCost = new Dictionary<State, double>();
            int cRepeated = 0;
            dCost[sStartState] = 0;
            dHeuristic[sStartState] = m_fHeuristic.h(sStartState);
            lOpenList.Add(sStartState);
            dParents[sStartState] = null;
            dGeneratingAction[sStartState] = null;
            m_cObservedStates = 1;
            int cHandled = 0;
            while (lOpenList.Count > 0)
            {
                sCurrent = GetMinimalStateBFS(lOpenList, dHeuristic, dCost);
                cHandled++;
                //Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + cHandled + ", " + dHeuristic[sCurrent] + "," + lOpenList.Count);
                lOpenList.Remove(sCurrent);
                Dictionary<State, Action> dNextStates = m_fHeuristic.GetNextStates(sCurrent);
                foreach (State sNext in dNextStates.Keys)
                {
                    if (!dParents.ContainsKey(sNext))
                    {
                        m_cObservedStates++;
                        dParents[sNext] = sCurrent;
                        dGeneratingAction[sNext] = dNextStates[sNext];
                        if (sNext.Contains(fGoal))
                        {
                            List<Action> lPlan = CreatePlan(sNext, dParents, dGeneratingAction);
                            ValidatePlan(sStartState, lPlan);
                            return lPlan;
                        }
                        else
                        {
                            dCost[sNext] = dCost[sCurrent] + 1;
                            dHeuristic[sNext] = m_fHeuristic.h(sNext);
                            lOpenList.Add(sNext);
                        }
                    }
                    else if (sNext != null)
                        cRepeated++;
                }
            }
            return null;
        }

        private bool ValidatePlan(State sStartState, List<Action> lPlan)
        {
            State sCurrent = sStartState;
            foreach (Action a in lPlan)
                sCurrent = sCurrent.Apply(a);
            bool bValid = sCurrent.Contains(m_pProblem.Goal);
            return bValid;
        }

        private State GetMinimalStateBFS(IEnumerable<State> lOpenList, Dictionary<State, double> dHeuristic, Dictionary<State, double> dCost)
        {
            double dMin = Double.PositiveInfinity, dSum = 0.0;
            State sBest = null;
            List<State> lBestHeuristic = new List<State>();
            foreach (State s in lOpenList)
            {
                if (dHeuristic[s] < dMin)
                {
                    sBest = s;
                    dMin = dHeuristic[s];
                    lBestHeuristic = new List<State>();
                }
                if (dHeuristic[s] == dMin)
                {
                    lBestHeuristic.Add(s);
                }
            }
            dMin = Double.PositiveInfinity;
            List<State> lEqual = new List<State>();
            foreach (State s in lBestHeuristic)
            {
                dSum = dHeuristic[s] + dCost[s];
                if (dSum < dMin)
                {
                    sBest = s;
                    dMin = dSum;
                    lEqual = new List<State>();
                }
                if (dSum == dMin)
                {
                    lEqual.Add(s);
                }
            }
            return lEqual.First();
            /*
            if (lEqual.Count == 1)
                return sBest;
            dMin = double.PositiveInfinity;
            foreach (State s in lEqual)
            {
                if (dHeuristic[s] < dMin)
                {
                    sBest = s;
                    dMin = dHeuristic[s];
                }
            }
            
            return sBest;*/
        }

        private State GetMinimalStateDFS(IEnumerable<State> lOpenList, Dictionary<State, double> dHeuristic, Dictionary<State, double> dCost)
        {
            double dMin = Double.PositiveInfinity;
            State sBest = null;
            List<State> lBestHeuristic = new List<State>();
            foreach (State s in lOpenList.Reverse())
            {
                if (dHeuristic[s] < dMin)
                {
                    sBest = s;
                    dMin = dHeuristic[s];
                    lBestHeuristic = new List<State>();
                }
                if (dHeuristic[s] == dMin)
                {
                    lBestHeuristic.Add(s);
                }
            }

            return sBest;
        }

        private List<Action> CreatePlan(State sLast, Dictionary<State, State> dParents, Dictionary<State, Action> dGeneratingAction)
        {
            List<Action> lPlan = new List<Action>();
            State sCurrent = sLast;
            while (dParents[sCurrent] != null)
            {
                lPlan.Add(dGeneratingAction[sCurrent]);
                sCurrent = dParents[sCurrent];
            }
            lPlan.Reverse();
            return lPlan;
        }

        


    }
}
