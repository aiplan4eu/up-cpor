using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace PDDL
{
    abstract class VisualizationUnit
    {
        public abstract void Init(Domain d, Problem p);
        public abstract void UpdateState(BeliefState bs);
        public abstract void Dispose();
        public abstract void addObservation(Formula s);
        public abstract void addAction(string s);
    }
}
