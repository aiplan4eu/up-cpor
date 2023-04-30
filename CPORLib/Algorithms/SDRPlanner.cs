using CPORLib.FFCS;
using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using static CPORLib.Tools.Options;
using Action = CPORLib.PlanningModel.PlanningAction;

namespace CPORLib.Algorithms
{

    public class SDRPlanner : PlannerBase
    {
        private PartiallySpecifiedState CurrentState;
        private List<string> FutureActions;
        private int NextActionIndex;
        private bool ExpectingObservation;
        public string Error { get; private set; }
        public bool GoalReached { get { return CurrentState.IsGoalState(); } }


        public SDRPlanner(Domain domain, Problem problem): base(domain, problem)    
        {
            Options.ComputeCompletePlanTree = false;
            Options.AddAllKnownToGiven = true; //this is needed in, e.g., medpks010
            //Debug.WriteLine("Started online replanning for " + Domain.Name + ", " + DateTime.Now);
            //no deadend support for now
            BeliefState bsInitial = problem.GetInitialBelief();
            CurrentState = bsInitial.GetPartiallySpecifiedState();
            FutureActions = null;
            NextActionIndex= 0;
            ExpectingObservation = false;
        }

        
        public string GetAction()
        {
            Error = "";
            if (ExpectingObservation)
            {
                Error = "Expecting the observation received from the last action before computing a new action.";
                return null;
            }
            if (GoalReached)
            {
                Error = "Goal already reached, no additional actions should be executed.";
                return null;
            }
            bool bPreconditionFailure = false;
            if (FutureActions != null && NextActionIndex < FutureActions.Count)
            {
                string sAction = FutureActions[NextActionIndex];
                bool bPreconditionsHold = CurrentState.IsApplicable(sAction);
                //Console.WriteLine("SDR: Checking applicability of action " + sAction +" : " + bPreconditionsHold);
                if (bPreconditionsHold)
                    return sAction;
                else
                    bPreconditionFailure = true;
            }

            List<string> lPlan = Plan(CurrentState, bPreconditionFailure, out bool bDeadEndReached, out State sChosen);
            if (lPlan == null || lPlan.Count ==0)
            {
                Error = "Could not plan for the current state";
                return null;
            }
            FutureActions = lPlan;
            NextActionIndex = 0;
            return GetAction();
        }

        public bool SetObservation(string sObservation)
        {
            Error = "";
            if (GoalReached)
            {
                Error = "Goal already reached, no additional actions should be executed.";
                return false;
            }
            string sAction = FutureActions[NextActionIndex];
            string sRevisedActionName = sAction.Replace(Utilities.DELIMITER_CHAR, " ");
            string[] aName = Utilities.SplitString(sRevisedActionName, ' ');
            Action a = Problem.Domain.GroundActionByName(aName);
            if(a.Observe == null && sObservation != null)
            {
                Error = "Action was not a sensing action, null observation expected.";
                return false;
            }
            if (a.Observe != null && sObservation == null)
            {
                Error = "Sensing action executed, expecting an observation.";
                return false;
            }
            PartiallySpecifiedState psNext = CurrentState.Apply(a, sObservation);
                /*
            CurrentState.ApplyOffline(a, out bool bPreconditionFailure, out PartiallySpecifiedState psTrue
                , out PartiallySpecifiedState psFalse, true);
            if(bPreconditionFailure)
            {
                Error = "Could not execute the next action, preconditions do not hold.";
                return false;
            }
            bool bObservation = true;
            if (sObservation != null)
            {
                sObservation = sObservation.ToLower().Trim();
                bObservation = (sObservation == "true");
            }
            if(bObservation)
            {
                if(psTrue == null)
                {
                    Error = "The recevied observation is not consistent with the current state.";
                    return false;
                }
                CurrentState = psTrue;
            }
            else
            {
                if (psFalse == null)
                {
                    Error = "The recevied observation is not consistent with the current state.";
                    return false;
                }
                CurrentState = psFalse;
            }
                */
            if(psNext == null)
            {
                Error = "Failed to apply the action at the current state.";
                return false;
            }
            CurrentState = psNext;
            NextActionIndex++;
            if(NextActionIndex == FutureActions.Count || sObservation != null)
            {
                FutureActions = null;
                NextActionIndex = -1;
            }
            ExpectingObservation = false;
            return true;
        }

        public bool OnlineReplanning()
        {
            Console.WriteLine("Started online replanning for " + Domain.Name + ", " + DateTime.Now);


            bool bSampleDeadendState = Options.SampleDeadendState;

            BeliefState bsInitial = Problem.GetInitialBelief();
            bsInitial.UnderlyingEnvironmentState = null;
            State s = null;

            if (Problem.DeadEndList.Count == 0)
                bSampleDeadendState = false;

            s = bsInitial.ChooseState(true, bSampleDeadendState);

            ExecutionData.FinalStateDeadend = false;
            ExecutionData.InitialStateDeadend = false;

            foreach (Formula f in Problem.DeadEndList)
            {
                if (f.IsTrue(s.Predicates, false))
                    ExecutionData.InitialStateDeadend = true;
            }



            bool bPreconditionFailure = false;

            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState(), pssNext = null;
            List<State> lTrueStates = new List<State>();
            lTrueStates.Add(pssCurrent.UnderlyingEnvironmentState);
            List<string> lActions = new List<string>();

            List<List<string>> lExecutedPlans = new List<List<string>>();
            List<State> lChosen = new List<State>();

            TimeSpan tsTime;
            Formula fObserved = null;
            int cActions = 0;
            int cPlanning = 0;
            int cObservations = 0;

            bool bPlanEndedSuccessfully = false, bGoalReached = false, bDeadEndReached = false;
            DateTime dtStart = DateTime.Now;
            while (!bGoalReached && !bDeadEndReached)
            {
                State sChosen = null;

                if (StuckInLoopPlanBased(cActions, pssCurrent, lExecutedPlans))
                    throw new Exception("SDR is stuck in a loop");
                


                List<string> lPlan = Plan(pssCurrent, bPreconditionFailure, out bDeadEndReached, out sChosen);
                if (lPlan == null)
                    throw new Exception("Could not plan for the current state");

                
                cPlanning++;
                lChosen.Add(sChosen);
                bPlanEndedSuccessfully = true;

                lExecutedPlans.Add(new List<string>());

                if (lPlan != null)
                {
                    foreach (string sAction in lPlan)
                    {

                        if (!IsReasoningAction(sAction.ToLower()))
                        {
                            Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" +
                                Domain.Name + ": " + cActions + "/" + lPlan.Count + ", memory:" + Process.GetCurrentProcess().PrivateMemorySize64 / 1000000 + "MB        ");
                            Debug.WriteLine("");
                            TimeSpan ts = DateTime.Now - dtStart;
                            if (ts.TotalMinutes > 60)
                                throw new Exception("Execution taking too long");
                            Debug.WriteLine((int)(ts.TotalMinutes) + "," + cActions + ") " + Domain.Name + ", executing action " + sAction);

                            lExecutedPlans.Last().Add(sAction);
                            DateTime dtBefore = DateTime.Now;

                            pssNext = pssCurrent.Apply(sAction, out fObserved);

                            List<Formula> lDeadends = null;
                            if (pssNext != null)
                            {
                                bPreconditionFailure = false;
                                DeadEndExistence isDeadEnd = pssNext.IsDeadEndExistenceAll(out lDeadends);
                                if (isDeadEnd == DeadEndExistence.DeadEndTrue)
                                {
                                    pssCurrent = pssNext;
                                    bDeadEndReached = true;
                                    bPlanEndedSuccessfully = true;
                                    break;

                                }
                            }
                            if (pssNext == null )
                            {
                                bPlanEndedSuccessfully = false;
                                Debug.WriteLine(Domain.Name + ", cannot execute " + sAction);

                                
                                bPreconditionFailure = true;
                                break;
                            }
                            else
                            {
                                lTrueStates.Add(pssNext.UnderlyingEnvironmentState);

                                if (pssNext != null)
                                {
                                    lActions.Add(sAction);

                                    if (SDR_OBS)
                                    {
                                        List<Action> lObservationActions = bsInitial.Problem.Domain.GroundAllObservationActions(pssNext.Observed, true);
                                        foreach (Action a in lObservationActions)
                                        {
                                            Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                                            if (!pssNext.Observed.Contains(pObserve) && !pssNext.Observed.Contains(pObserve.Negate()))
                                            {
                                                pssNext = pssNext.Apply(a, out fObserved);
                                                lActions.Add(a.Name);
                                                cObservations++;
                                                Debug.WriteLine(Domain.Name + ", observed " + fObserved);
                                                cActions++;
                                            }
                                        }
                                    }
                                    cActions++;
                                    pssCurrent = pssNext;
                                    if (fObserved != null)
                                    {
                                        cObservations++;
                                        Debug.WriteLine(Domain.Name + ", observed " + fObserved);

                                    }
                                }
                                else
                                {
                                    //Debug.WriteLine("Skipping inapplicable KW action...");
                                }
                            }
                        }
                    }
                }

                if (bDeadEndReached)
                {
                    DateTime dtBefore = DateTime.Now;
                    Debug.WriteLine("Dead End time: " + (DateTime.Now - dtBefore).TotalSeconds);
                    ExecutionData.FinalStateDeadend = true;
                }
                if (bPlanEndedSuccessfully)
                {
                    DateTime dtBefore = DateTime.Now;
                    bGoalReached = pssCurrent.IsGoalState();
                    Debug.WriteLine("Goal time: " + (DateTime.Now - dtBefore).TotalSeconds);
                }
                else
                {
                    GroundedPredicate gpDead = new GroundedPredicate("dead");
                    if (pssCurrent.Observed.Contains(gpDead))
                        bGoalReached = true;

                }
            }
            bool bValid = pssCurrent.IsGoalState();
            if (!bValid)
                bValid = pssCurrent.IsDeadEndState() == Options.DeadEndExistence.DeadEndTrue;


            tsTime = DateTime.Now - dtStart;

            int cHistory = 0;
            PartiallySpecifiedState pssIt = pssCurrent;
            while (pssIt != null)
            {
                pssIt = pssIt.Predecessor;
                cHistory++;
            }
            cActions = cHistory;

            ExecutionData.Actions = cActions;
            ExecutionData.Planning = cPlanning;
            ExecutionData.Observations = cObservations;
            ExecutionData.Time = DateTime.Now - dtStart;

            Console.WriteLine("Actions: " + cHistory);
            Console.WriteLine("Average time - " + tsTime.TotalSeconds * 1.0 / cActions);
            Console.WriteLine("Total time - " + tsTime.TotalSeconds);
            Console.WriteLine("*******************************************************************************");

            return bValid;
        }


        

    }
}
