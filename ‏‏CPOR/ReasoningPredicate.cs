using System;
using System.Collections.Generic;

namespace CPOR
{
    class ReasoningPredicate : Predicate
    {
        public string Operator { get; private set; }
        public List<Predicate> Predicates { get; private set; }
        public ReasoningPredicate(string sOperator)
            : base("Reasoning-" + sOperator)
        {
            Operator = sOperator;
            Predicates = new List<Predicate>();
        }
        public ReasoningPredicate(CompoundFormula cf)
            : base("Reasoning-" + cf.Operator)
        {
            Operator = cf.Operator;
            Predicates = new List<Predicate>();
            foreach (Formula f in cf.Operands)
            {
                if (f is PredicateFormula)
                {
                    Predicates.Add(((PredicateFormula)f).Predicate);
                }
                else
                {
                    Predicates.Add(new ReasoningPredicate((CompoundFormula)f));
                }
            }
        }
        public override bool ConsistentWith(Predicate pState)
        {
            throw new NotImplementedException();
        }

        public override Predicate Negate()
        {
            ReasoningPredicate pNegate = null;
            if (Operator == "or")
                pNegate = new ReasoningPredicate("and");
            if (Operator == "and")
                pNegate = new ReasoningPredicate("or");
            if (Operator == "oneof")
                throw new NotImplementedException("Not handling oneof for now");
            if (Operator == "not")
                return Predicates[0];
            foreach (Predicate fOperand in Predicates)
                pNegate.Predicates.Add(fOperand.Negate());
            return pNegate;
        }

        public Predicate Reduce(List<Predicate> lObserved)
        {
            List<Predicate> lTemp = new List<Predicate>(Predicates);
            foreach (Predicate p in lTemp)
            {
                if (p.IsContainedIn(lObserved))
                {
                    if (Operator == "or")
                        return null;//reasoning predicate no longer informative
                    else if (Operator == "and")
                        Predicates.Remove(p);
                    else if (Operator == "oneof")
                    {//(oneof a b c) and a = (and !b !c)
                        Operator = "and";
                        List<Predicate> lPredicates = new List<Predicate>();
                        foreach (Predicate pOther in Predicates)
                        {
                            if (!pOther.Equals(p))
                                lPredicates.Add(pOther.Negate());
                        }
                        Predicates = lPredicates;
                    }
                    else
                        throw new NotImplementedException();
                }
                else if (Predicates.Contains(p.Negate()))
                {
                    if (Operator == "or")
                    {
                        Predicates.Remove(p.Negate());
                    }
                    else if (Operator == "and")
                    {
                        throw new InvalidOperationException("Inconsistent predicate");
                    }
                    else if (Operator == "oneof")
                    {
                        Predicates.Remove(p.Negate());
                    }
                    else
                        throw new NotImplementedException();
                }

            }
            if (Predicates.Count == 0)
                return null;//no longer informative
            if (Predicates.Count == 1)
                return Predicates[0];
            return this;
        }

        public override bool IsContainedIn(List<Predicate> lPredicates)
        {
            throw new NotImplementedException();
        }

        public override Predicate GenerateKnowGiven(string sTag, bool bKnowWhether)
        {
            throw new NotImplementedException();
        }
        public override Predicate GenerateGiven(string sTag)
        {
            throw new NotImplementedException();
        }

        protected override string GetString()
        {
            throw new NotImplementedException();
        }

        public override Predicate ToTag()
        {
            throw new NotImplementedException();
        }

        public override int Similarity(Predicate p)
        {
            throw new NotImplementedException();
        }

        public override bool SameInvariant(Predicate p, Argument aInvariant)
        {
            throw new NotImplementedException();
        }

        protected override int ComputeHashCode()
        {
            throw new NotImplementedException();
        }

        public override Predicate Clone()
        {
            throw new NotImplementedException();
        }
    }
}
