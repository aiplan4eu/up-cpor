
using System;
using System.Collections.Generic;

namespace CPORLib.LogicalUtilities
{
    class KnowWhetherPredicate : Predicate
    {
        public Predicate Knowledge { get; private set; }
        public KnowWhetherPredicate(Predicate p)
            : base("KW" + p.Name)
        {
            if (p.Negation)
            {
                Knowledge = p.Negate();
            }
            else
            {
                Knowledge = p;
            }
        }

        public override bool ConsistentWith(Predicate pState)
        {
            throw new NotImplementedException();
        }

        public override Predicate Negate()
        {
            KnowWhetherPredicate kpNegate = new KnowWhetherPredicate(Knowledge);
            kpNegate.Negation = !Negation;
            return kpNegate;
        }

        public override bool IsContainedIn(List<Predicate> lPredicates)
        {
            throw new NotImplementedException();
        }
        public override bool Equals(object obj)
        {
            if (obj is KnowWhetherPredicate)
            {
                KnowWhetherPredicate kp = (KnowWhetherPredicate)obj;
                if (Negation == kp.Negation)
                    return Knowledge.Equals(kp.Knowledge);
            }
            return false;
        }
        protected override string GetString()
        {
            string s = "";
            if (Negation)
                s += "(not ";
            //s += "(K" + Knowledge.Name;
            s += "(" + Name;
            if (Knowledge is ParametrizedPredicate)
            {
                foreach (Argument a in ((ParametrizedPredicate)Knowledge).Parameters)
                    s += " " + a.Name;
            }
            if (Knowledge is GroundedPredicate)
            {
                foreach (Constant c in ((GroundedPredicate)Knowledge).Constants)
                    s += " " + c.Name;
            }
            s += ")";
            if (Negation)
                s += ")";
            return s;
        }

        public override Predicate GenerateKnowGiven(string sTag, bool bKnowWhether)
        {
            throw new NotImplementedException();
        }
        public override Predicate GenerateGiven(string sTag)
        {
            throw new NotImplementedException();
        }

        public GroundedPredicate Ground(Dictionary<string, Constant> dBindings)
        {
            GroundedPredicate gp = new GroundedPredicate("K" + Knowledge.Name);
            if (Knowledge is ParametrizedPredicate)
            {
                foreach (Argument a in ((ParametrizedPredicate)Knowledge).Parameters)
                {
                    if (a is Parameter)
                    {
                        if (dBindings.ContainsKey(a.Name))
                            gp.AddConstant(dBindings[a.Name]);
                        else
                            throw new NotImplementedException();
                    }
                    else
                        gp.AddConstant((Constant)a);
                }
            }
            else
            {
                foreach (Constant c in ((GroundedPredicate)Knowledge).Constants)
                {
                    gp.AddConstant(c);
                }
            }
            return gp;
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
