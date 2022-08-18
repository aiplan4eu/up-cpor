using System.Collections.Generic;
using Action = CPORLib.PlanningModel.PlanningAction;
using CPORLib.PlanningModel;


namespace CPORLib.Algorithms
{
    abstract class HeuristicFunction
    {
        public abstract double h(State s);
        public abstract Dictionary<State, Action> GetNextStates(State s);
    }
}
