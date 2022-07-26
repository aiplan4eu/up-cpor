﻿using System.Collections.Generic;
using Action = CPORLib.PlanningModel.PlanningAction;
using CPORLib.PlanningModel;

namespace CPORLib.Algorithms
{
    public abstract class Planner
    {
        protected Domain m_dDomain;
        protected Problem m_pProblem;
        public Planner(Domain d, Problem p)
        {
            m_dDomain = d;
            m_pProblem = p;
        }

        public abstract List<string> Plan(State s);
    }
}
