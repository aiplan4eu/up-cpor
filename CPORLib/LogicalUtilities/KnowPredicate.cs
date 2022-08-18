
using System;
using System.Collections.Generic;
using CPORLib.Tools;


namespace CPORLib.LogicalUtilities
{
    class KnowPredicate : Predicate
    {
        public Predicate Knowledge { get; private set; }
        public bool Value { get; private set; }
        public bool Parametrized { get; set; }


        public KnowPredicate(Predicate p)
            : this(p, !p.Negation, false)
        {

        }
        public KnowPredicate(KnowPredicate kp) : base(kp.Name)
        {
            Knowledge = kp.Knowledge;
            Value = kp.Value;
            Parametrized = kp.Parametrized;

        }
        public KnowPredicate(Predicate p, bool bValue, bool bParametrized)
            : base("N/A")
        {
            if (bValue)
                Name = "K" + p.Name;
            else
                Name = "KN" + p.Name;
            Parametrized = bParametrized;
            Value = bValue;
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
            /*
            KnowPredicate kpNegate = new KnowPredicate(Knowledge, Value, Parametrized);
            kpNegate.Negation = !Negation;
            return kpNegate;
             */
            KnowPredicate kpNegate = new KnowPredicate(this);
            kpNegate.Negation = !Negation;
            return kpNegate;

        }

        public override bool IsContainedIn(List<Predicate> lPredicates)
        {
            throw new NotImplementedException();
        }
        public override bool Equals(object obj)
        {
            if (obj is KnowPredicate)
            {
                KnowPredicate kp = (KnowPredicate)obj;
                if (Value == kp.Value && Negation == kp.Negation)
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
            /*
            if (Parametrized)
                s += " " + Utilities.VALUE_PARAMETER;
            else
            {
                if (Value)
                    s += " " + Utilities.TRUE_VALUE;
                else
                    s += " " + Utilities.FALSE_VALUE;
            }        
            */
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

        public GroundedPredicate Ground(Dictionary<Parameter, Constant> dBindings)
        {
            GroundedPredicate gp = new GroundedPredicate("K" + Knowledge.Name);
            if (Knowledge is ParametrizedPredicate)
            {
                foreach (Argument a in ((ParametrizedPredicate)Knowledge).Parameters)
                {
                    if (a is Parameter p)
                    {
                        if (dBindings.ContainsKey(p))
                            gp.AddConstant(dBindings[p]);
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
            if (Parametrized)
            {
                //if (dBindings.ContainsKey(Utilities.VALUE_PARAMETER))
                ///    gp.AddConstant(dBindings[Utilities.VALUE_PARAMETER]);
                //else
                throw new NotImplementedException();
            }
            else
            {
                if (Value)
                    gp.AddConstant(new Constant(Utilities.VALUE, Utilities.TRUE_VALUE));
                else
                    gp.AddConstant(new Constant(Utilities.VALUE, Utilities.FALSE_VALUE));
            }
            return gp;
        }


        public override Predicate ToTag()
        {
            KnowPredicate ppNew = new KnowPredicate(this);
            if (Negation)
                ppNew.Name = ppNew.Name + "-Remove";
            else
                ppNew.Name = ppNew.Name + "-Add";
            ppNew.Negation = false;
            return ppNew;
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
            int iCode = Knowledge.GetHashCode() * 10;
            if (Value)
                iCode += 1;
            return iCode;
        }

        public override Predicate Clone()
        {
            throw new NotImplementedException();
        }
    }
}
