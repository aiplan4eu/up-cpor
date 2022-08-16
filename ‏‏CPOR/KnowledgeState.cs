using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    public class KnowledgeState : State
    {
        public KnowledgeState(Problem p)
            : base(p)
        {
        }
        public KnowledgeState(KnowledgeState ksPredecessor)
            : base(ksPredecessor)
        {
        }

        public override void GroundAllActions()
        {
            AvailableActions = Problem.Domain.GroundAllActions(m_lPredicates, true);
            HashSet<Predicate> lKnowPredicates = new HashSet<Predicate>();
            foreach (CompoundFormula cf in Problem.Hidden)
            {
                cf.GetAllPredicates(lKnowPredicates);
            }
            AddKnowledgePredicatesToExistingActions(lKnowPredicates);
            AddReasoningActions();
        }

        private CompoundFormula AddKnowledgePredicatesToFormula(Formula f, HashSet<Predicate> lKnowPredicates)
        {
            CompoundFormula cf = new CompoundFormula("and");
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            f.GetAllPredicates(lPredicates);
            foreach (Predicate p in lPredicates)
            {
                if (lKnowPredicates.Contains(p))
                {
                    KnowPredicate kp = new KnowPredicate(p);
                    cf.AddOperand(new PredicateFormula(kp));
                }
            }
            if (f is CompoundFormula && ((CompoundFormula)f).Operator == "and")
            {
                foreach (Formula fSub in ((CompoundFormula)f).Operands)
                    cf.AddOperand(fSub);
            }
            else
                cf.AddOperand(f);
            return cf;
        }

        //problem - we have to be over restrictive:
        //(xor a b c) + know(a) + know(b) = know(c)
        private void AddReasoningActions()
        {
            foreach (CompoundFormula cf in Problem.Hidden)
            {
                AvailableActions.AddRange(CreateReasoningActions(cf));
            }
        }

        private Action CreateReasoningAction(Predicate pEffect, HashSet<Predicate> lPredicates)
        {
            KnowPredicate kpEffect = new KnowPredicate(pEffect);
            if (Predicates.Contains(kpEffect))
                return null;
            Action a = new KnowledgeAction("Reasoning_" + pEffect.ToString());
            a.Preconditions = new CompoundFormula("and");
            foreach (Predicate pOther in lPredicates)
            {
                if (pOther != pEffect)
                {
                    KnowPredicate kp = new KnowPredicate(pOther);
                    if (!Predicates.Contains(kp))
                        return null;
                    ((CompoundFormula)a.Preconditions).AddOperand(new PredicateFormula(kp));
                }
            }
            CompoundFormula cfEffects = new CompoundFormula("and");
            cfEffects.AddOperand(new PredicateFormula(kpEffect));
            a.SetEffects(cfEffects);
            return a;
        }

        private List<Action> CreateReasoningActions(CompoundFormula cf)
        {
            List<Action> lActions = new List<Action>();
            Action a = null;
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cf.GetAllPredicates(lPredicates);
            foreach (Predicate p in lPredicates)
            {
                a = CreateReasoningAction(p, lPredicates);
                if (a != null)
                    lActions.Add(a);
            }
            return lActions;
        }

        private void AddKnowledgePredicatesToExistingActions(HashSet<Predicate> lKnowPredicates)
        {
            List<Action> lActions = AvailableActions;
            AvailableActions = new List<Action>();
            foreach (Action a in lActions)
            {
                KnowledgeAction ka = new KnowledgeAction(a);
                ka.Preconditions = AddKnowledgePredicatesToFormula(a.Preconditions, lKnowPredicates);
                CompoundFormula cfEffects = null;
                if (Contains(ka.Preconditions))
                {
                    if (a.Effects != null)
                    {
                        cfEffects = AddKnowledgePredicatesToFormula(a.Effects, lKnowPredicates);
                    }
                    else
                    {
                        cfEffects = new CompoundFormula("and");
                    }
                    if (a.Observe != null)
                    {
                        HashSet<Predicate> lPredicates = new HashSet<Predicate>();
                        a.Observe.GetAllPredicates(lPredicates);
                        foreach (Predicate p in lPredicates)
                        {
                            cfEffects.AddOperand(new PredicateFormula(new KnowPredicate(p)));
                        }
                        ka.Observe = null;
                    }
                    ka.SetEffects(cfEffects);
                    if (!Contains(ka.Effects))
                        AvailableActions.Add(ka);
                }
            }
        }

        public override State Clone()
        {
            return new KnowledgeState((KnowledgeState)this);
        }


        public void WriteKnowledgeProblem(string sFileName, BeliefState bs)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (problem K" + Problem.Name + ")");
            sw.WriteLine("(:domain K" + Problem.Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            /*
            foreach (GroundedPredicate gpKnow in Problem.Known)
            {
                sw.Write("(K" + gpKnow.Name);
                foreach (Constant c in gpKnow.Constants)
                    sw.Write(" " + c.Name);
                sw.WriteLine(")");
            }
             * */
            foreach (GroundedPredicate gp in bs.Observed)
            {
                sw.Write("(K" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write(" " + c.Name);
                sw.WriteLine(")");
            }
            foreach (GroundedPredicate gp in Predicates)
            {
                sw.Write("(" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write(" " + c.Name);
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            Problem.Goal.GetAllPredicates(lGoalPredicates);
            string sGoal = Problem.Goal.ToString();
            sw.WriteLine("(:goal " + sGoal + ")");
            /* Not sure whether we have to KNOW that we have the goal
            sw.Write("(:goal (and " + sGoal);
            foreach (Predicate p in lGoalPredicates)
                Problem.Domain.WriteKnowledgePredicate(sw, p);
            sw.WriteLine("))");
             */
            sw.WriteLine(")");
            sw.Close();
        }

        internal void WriteTaggedProblem(string p, BeliefState bsCurrent)
        {
            throw new NotImplementedException();
        }
    }
}
