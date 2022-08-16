using System.Collections.Generic;

namespace CPOR
{
    class KnowledgeDomain : Domain
    {
        public List<Action> KnowledgeActions { get; private set; }
        public KnowledgeDomain(Domain d, Problem p)
            : base("K" + d.Name, d.Path)
        {
            KnowledgeActions = new List<Action>();
            CreateKnowledgeActions(d, p);
        }

        private void CreateKnowledgeActions(Domain d, Problem p)
        {
            List<Predicate> lKnowPredicates = new List<Predicate>();
            foreach (CompoundFormula cf in p.Hidden)
            {
                GetAllPredicates(cf, lKnowPredicates);
            }
            //CreateConstants(d, lKnowPredicates);
            AddKnowledgePredicatesToExistingActions(d, lKnowPredicates);
            AddReasoningActions(p);
        }

        private CompoundFormula AddKnowledgePredicatesToFormula(Formula f, List<Predicate> lKnowPredicates)
        {
            CompoundFormula cf = new CompoundFormula("and");
            List<Predicate> lPredicates = GetAllPredicates(f);
            foreach (Predicate p in lPredicates)
            {
                if (lKnowPredicates.Contains(p))
                    cf.AddOperand(new PredicateFormula(new KnowPredicate(p)));
            }
            cf.AddOperand(f);
            return cf;
        }

        //problem - we have to be over restrictive:
        //(xor a b c) + know(a) + know(b) = know(c)
        private void AddReasoningActions(Problem p)
        {
            foreach (CompoundFormula cf in p.Hidden)
            {
                Actions.AddRange(CreateReasoningActions(cf));
            }
        }

        private List<Action> CreateReasoningActions(CompoundFormula cf)
        {
            List<Action> lActions = new List<Action>();
            Action a = null;
            List<Predicate> lPredicates = GetAllPredicates(cf);
            foreach (Predicate p in lPredicates)
            {
                a = new Action(cf.ToString() + "_" + p.ToString());
                a.Preconditions = new CompoundFormula("and");
                CompoundFormula cfEffects = new CompoundFormula("and");
                cfEffects.AddOperand(new PredicateFormula(new KnowPredicate(p)));
                foreach (Predicate pOther in lPredicates)
                {
                    if (pOther != p)
                        ((CompoundFormula)a.Preconditions).AddOperand(new PredicateFormula(new KnowPredicate(pOther)));
                }
                a.SetEffects(cfEffects);
                lActions.Add(a);
            }
            return lActions;
        }

        private void AddKnowledgePredicatesToExistingActions(Domain d, List<Predicate> lKnowPredicates)
        {
            Actions = new List<Action>();
            ParametrizedAction aRevised = null;
            foreach (Action a in d.Actions)
            {
                aRevised = new ParametrizedAction(a.Name);
                aRevised.Preconditions = AddKnowledgePredicatesToFormula(a.Preconditions, lKnowPredicates);
                CompoundFormula cfEffects = null;
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
                    List<Predicate> lPredicates = GetAllPredicates(a.Observe);
                    foreach (Predicate p in lPredicates)
                    {
                        cfEffects.AddOperand(new PredicateFormula(new KnowPredicate(p)));
                    }
                }
                aRevised.SetEffects(cfEffects);
                Actions.Add(aRevised);
            }
        }
        /*
        private void CreateConstants(Domain d, List<Predicate> lKnowPredicates)
        {
            foreach (Constant c in d.Constants)
                Constants.Add(c);
            foreach (Predicate p in lKnowPredicates)
                Constants.Add(new Constant("Know", p.ToString()));
        }
         * */
        private List<Predicate> GetAllPredicates(Formula f)
        {
            List<Predicate> lPredicates = new List<Predicate>();
            GetAllPredicates(f, lPredicates);
            return lPredicates;
        }

        private void GetAllPredicates(Formula f, List<Predicate> lPredicates)
        {
            if (f is PredicateFormula)
            {
                if (!lPredicates.Contains(((PredicateFormula)f).Predicate))
                    lPredicates.Add(((PredicateFormula)f).Predicate);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                foreach (Formula fSub in cf.Operands)
                    GetAllPredicates(fSub, lPredicates);
            }
        }
    }
}
