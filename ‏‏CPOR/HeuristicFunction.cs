using System.Collections.Generic;

namespace CPOR
{
    abstract class HeuristicFunction
    {
        public abstract double h(State s);
        public abstract Dictionary<State, Action> GetNextStates(State s);
    }
}
