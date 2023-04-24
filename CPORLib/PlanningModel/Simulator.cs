using CPORLib.LogicalUtilities;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Text;

namespace CPORLib.PlanningModel
{
    public class Simulator
    {
        private Domain Domain;
        private Problem Problem;
        private BeliefState InitialBelief;
        private State InitialChosenState;
        private PartiallySpecifiedState CurrentState;


        public Simulator(Domain d, Problem p)
        {
            Domain = d;
            Problem = p;
            Reset();
        }

        public string Apply(PlanningAction a)
        {
            PartiallySpecifiedState psNext = CurrentState.Apply(a, out Formula fObserve);
            if (psNext == null)
                throw new Exception("Action " + a.Name + " is not applicable in the current belief state");
            CurrentState = psNext;
            if (a.Observe == null)
                return null;
            return fObserve.ToString();
        }

        public string Apply(string sAction)
        {
            string[] aName = Utilities.SplitString(sAction, ' ');
            PlanningAction a = Domain.GroundActionByName(aName);
            if (a == null)
                throw new Exception("Invalid action name: " + sAction);
            return Apply(a);
        }
        public bool GoalReached
        {
            get { return CurrentState.IsGoalState();}
        }
        
        public void Reset()
        {
            InitialBelief = Problem.GetInitialBelief();
            InitialChosenState = InitialBelief.ChooseState(true);
            CurrentState = new PartiallySpecifiedState(InitialBelief);
        }
    }
}
