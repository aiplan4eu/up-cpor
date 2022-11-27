using CPORLib.LogicalUtilities;
using CPORLib.PlanningModel;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Action = CPORLib.PlanningModel.PlanningAction;

namespace CPORLib.Algorithms
{
    public class BFSSolver
    {
        public List<Action> SolveII(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<State> lOpenList = new List<State>();
            lOpenList.Add(sStart);
            State sCurrent = null, sNext = null;
            Dictionary<State, Action> dMapStateToGeneratingAction = new Dictionary<State, Action>();
            dMapStateToGeneratingAction[sStart] = null;
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            Dictionary<State, int> dDepth = new Dictionary<State, int>();
            dDepth[sStart] = 0;
            dParents[sStart] = null;
            int cProcessed = 0;
            List<string> lActionNames = new List<string>();
            while (lOpenList.Count > 0)
            {
                sCurrent = lOpenList[0];
                lOpenList.RemoveAt(0);
                List<Action> lActions = d.GroundAllActions(sCurrent.Predicates, false);
                foreach (Action a in lActions)
                {
                    sNext = sCurrent.Apply(a);
                    bool bGiven = false;
                    foreach (Predicate pGiven in sNext.Predicates)
                    {
                        if (pGiven.Name.ToLower().Contains("given"))
                            bGiven = true;
                    }
                    if (!lActionNames.Contains(a.Name))
                        lActionNames.Add(a.Name);
                    if (sNext != null && p.IsGoalState(sNext))
                        return GeneratePlan(sCurrent, a, dParents, dMapStateToGeneratingAction);
                    if (!dParents.Keys.Contains(sNext))
                    {
                        dDepth[sNext] = dDepth[sCurrent] + 1;
                        dParents[sNext] = sCurrent;
                        dMapStateToGeneratingAction[sNext] = a;
                        lOpenList.Add(sNext);
                    }
                }
                cProcessed++;
                if (cProcessed % 10 == 0)
                    Debug.WriteLine(cProcessed + ") " + dDepth[sCurrent] + "," + lOpenList.Count);
            }
            return null;
        }

        public List<Action> ManualSolve(Problem p, Domain d, bool bApplyAllMerges)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            State sCurrent = null, sNext = null;
            Dictionary<State, Action> dMapStateToGeneratingAction = new Dictionary<State, Action>();
            dMapStateToGeneratingAction[sStart] = null;
            Dictionary<State, State> dParents = new Dictionary<State, State>();
            dParents[sStart] = null;
            int cProcessed = 0;
            List<string> lActionNames = new List<string>();

            sCurrent = sStart;
            while (!p.IsGoalState(sCurrent))
            {
                List<Action> lActions = d.GroundAllActions(sCurrent.Predicates, false);
                if (bApplyAllMerges)
                {
                    List<Action> lActionsNoMerges = new List<Action>();
                    foreach (Action aCurrent in lActions)
                    {
                        if (aCurrent.Name.ToLower().StartsWith("merge") || aCurrent.Name.ToLower().StartsWith("refute"))
                        {
                            Console.WriteLine("Applying reasoning action: " + aCurrent.Name);
                            sCurrent = sCurrent.Apply(aCurrent);

                        }
                        else
                            lActionsNoMerges.Add(aCurrent);
                    }
                    lActions = lActionsNoMerges;
                }
                Console.WriteLine("\nAvailable actions:");
                for (int i = 0; i < lActions.Count; i++)
                {
                    Action ac = lActions[i];
                    if (ac.Preconditions == null || ac.Preconditions.IsTrue(sCurrent.Predicates, sCurrent.MaintainNegations))
                        Console.WriteLine(i + ") " + ac.Name);
                }
                Console.Write("Choose action number: ");
                int iAction = int.Parse(Console.ReadLine());
                Action a = lActions[iAction];
                sNext = sCurrent.Apply(a);

                foreach (Predicate pNew in sNext.Predicates)
                    if (!sCurrent.Predicates.Contains(pNew))
                        Console.WriteLine(pNew);

                if (!dParents.Keys.Contains(sNext))
                {
                    dParents[sNext] = sCurrent;
                    dMapStateToGeneratingAction[sNext] = a;
                }

                sCurrent = sNext;

                cProcessed++;
            }
            return GeneratePlan(sCurrent, null, dParents, dMapStateToGeneratingAction);
        }


        public List<Action> RadnomSolve(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = d.GroundAllActions(sStart.Predicates, false);
            int iRnd = RandomGenerator.Next(lActions.Count);
            List<Action> lPlan = new List<Action>();
            lPlan.Add(lActions[iRnd]);
            return lPlan;
        }

        public List<Action> Solve(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = new List<Action>();
            Action aClear = d.GroundActionByName(new string[] { "clear-all", "" }, sStart.Predicates, false);
            sStart = sStart.Apply(aClear);
            lActions.Add(aClear);
            State sComputeUpstream = ApplyCompute(sStart, "upstream", lActions, d);
            State sComputeAffected = ApplyCompute(sComputeUpstream, "affected", lActions, d);
            State sComputePath = ApplyCompute(sComputeAffected, "path", lActions, d);
            State sComputeLine = ApplyCompute(sComputePath, "line", lActions, d);
            //State sObserveAll = ObserveAll(sComputeLine, lActions, d);
            return lActions;
        }

        public List<Action> SolveOld(Problem p, Domain d)
        {
            State sStart = p.GetInitialBelief().ChooseState(true);
            List<Action> lActions = new List<Action>();
            State sObserved = ObserveAll(sStart, lActions, d);
            State sFixed = ApplyAxiom(sObserved, lActions, d);
            //State sClosed = CloseAll(sFixed, lActions, d);
            //State sFixed2 = ApplyAxiom(sClosed, lActions, d);
            State sObserved2 = ObserveAll(sFixed, lActions, d);
            return lActions;
        }

        private State CloseAll(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            List<Action> l = d.GroundAllActions(s.Predicates, false);
            foreach (Action a in l)
            {
                if (a.Name.Contains("close"))
                {
                    sCurrent = sCurrent.Apply(a);
                    lActions.Add(a);
                }
            }
            return sCurrent;
        }

        private State ApplyCompute(State s, string sName, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            Predicate pNew = new GroundedPredicate("new-" + sName);
            Predicate pDone = new GroundedPredicate("done-" + sName);
            int i = 0;
            while (!sCurrent.Contains(pNew.Negate()) || !sCurrent.Contains(pDone) || i < 10)
            {
                Action a1 = d.GroundActionByName(new string[] { "pre-" + sName, "" }, sCurrent.Predicates, false);
                Action a2 = d.GroundActionByName(new string[] { "compute-" + sName, "" }, sCurrent.Predicates, false);
                if (a1 != null && a2 != null)
                {
                    sCurrent = sCurrent.Apply(a1);
                    sCurrent = sCurrent.Apply(a2);
                    lActions.Add(a1);
                    lActions.Add(a2);
                }
                i++;
            }

            Action a = d.GroundActionByName(new string[] { "observe-new-" + sName + "-F", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            a = d.GroundActionByName(new string[] { "post-" + sName, "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            return sCurrent;
        }

        private State ApplyAxiom(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            Predicate pNew = new GroundedPredicate("new");
            Predicate pDone = new GroundedPredicate("done");
            while (!sCurrent.Contains(pNew.Negate()) || !sCurrent.Contains(pDone))
            {
                Action a1 = d.GroundActionByName(new string[] { "pre-axiom", "" }, sCurrent.Predicates, false);
                Action a2 = d.GroundActionByName(new string[] { "axiom", "" }, sCurrent.Predicates, false);
                if (a1 != null && a2 != null)
                {
                    sCurrent = sCurrent.Apply(a1);
                    sCurrent = sCurrent.Apply(a2);
                    lActions.Add(a1);
                    lActions.Add(a2);
                }
            }

            Action a = d.GroundActionByName(new string[] { "observe-new-F", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            a = d.GroundActionByName(new string[] { "fixpoint", "" }, sCurrent.Predicates, false);
            sCurrent = sCurrent.Apply(a);
            lActions.Add(a);

            return sCurrent;
        }

        private State ObserveAll(State s, List<Action> lActions, Domain d)
        {
            State sCurrent = s;
            List<Action> l = d.GroundAllActions(s.Predicates, false);
            foreach (Action a in l)
            {
                if (a.Name.Contains("observe"))
                {
                    sCurrent = sCurrent.Apply(a);
                    lActions.Add(a);
                }
            }
            return sCurrent;
        }

        private List<Action> GeneratePlan(State sBeforeLast, Action aLast, Dictionary<State, State> dParents, Dictionary<State, Action> dMapStateToGeneratingAction)
        {
            List<Action> lPlan = new List<Action>();
            State sCurrent = sBeforeLast;
            lPlan.Add(aLast);
            while (dParents[sCurrent] != null)
            {
                Action a = dMapStateToGeneratingAction[sCurrent];
                lPlan.Add(a);
                sCurrent = dParents[sCurrent];
            }
            lPlan.Reverse();
            return lPlan;
        }
    }
}
