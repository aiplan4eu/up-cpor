using System;
using CPORLib.Tools;
using System.Collections.Generic;
using System.Linq;

namespace CPORLib.LogicalUtilities
{
    public class GroundedPredicate : Predicate
    {
        public List<Constant> Constants { get; protected set; }
        public static GroundedPredicate pFalsePredicate = Utilities.FALSE_PREDICATE;
        public static GroundedPredicate pTruePredicate = Utilities.TRUE_PREDICATE;
        private GroundedPredicate m_gpNegation;
        public GroundedPredicate(string sName)
            : base(sName)
        {
            //if (sName == Utilities.FALSE_PREDICATE)
            //    Debug.WriteLine("Initialized  a false predicate");
            m_gpNegation = null;
            Constants = new List<Constant>();
        }
        public GroundedPredicate(string sName, bool bNegate)
             : base(sName)
        {
            //if (sName == Utilities.FALSE_PREDICATE)
            //    Debug.WriteLine("Initialized  a false predicate");
            Negation = bNegate;
            m_gpNegation = null;
            Constants = new List<Constant>();
        }
        public GroundedPredicate(GroundedPredicate gpOther)
            : base(gpOther.Name, gpOther.Negation)
        {
            Constants = new List<Constant>(gpOther.Constants);
        }
        protected override string GetString()
        {
            string s = "(" + Name + " " + Utilities.ListToString(Constants) + ")";
            if (Negation)
                s = "(not " + s + ")";
            return s;
        }


        private bool ComputeEquals(object obj)
        {
            if (obj is PredicateFormula)
            {
                obj = ((PredicateFormula)obj).Predicate;
            }
            if (obj is GroundedPredicate)
            {
                //bool bSame = GetHashCode() == obj.GetHashCode();
                //return bSame;
                GroundedPredicate gp = (GroundedPredicate)obj;
                if (gp.Negation != Negation)
                    return false;
                if (Name != gp.Name)
                    return false;
                if (Constants.Count != gp.Constants.Count)
                    return false;
                for (int i = 0; i < Constants.Count; i++)
                {
                    if (Constants[i].Name != gp.Constants[i].Name)
                        return false;
                }
                return true;
            }
            return false;
        }
        public override bool Equals(object obj)
        {
            bool bSame2 = ComputeEquals(obj);
            return bSame2;

        }

        public Dictionary<Parameter, Constant> Bind(ParametrizedPredicate p)
        {
            if (Name != p.Name)
                return null;

            if (Constants.Count != ((List<Argument>)p.Parameters).Count)
                return null;

            Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();

            for (int i = 0; i < Constants.Count; i++)
            {
                Argument arg = p.Parameters.ElementAt(i);
                if (arg is Constant)
                {
                    if (!Constants[i].Equals(arg))
                        return null;
                }
                if (arg is Parameter param)
                    dBindings[param] = Constants[i];
            }
            return dBindings;
        }


        public override bool ConsistentWith(Predicate p)
        {
            if (Name != p.Name)
                return true; //irrelvant predicate - no contradiction
            if (p is ParametrizedPredicate)
            {
                //TODO
                throw new NotImplementedException();
            }
            GroundedPredicate gp = (GroundedPredicate)p;
            if (Constants.Count != gp.Constants.Count)
                return true;
            for (int i = 0; i < Constants.Count; i++)
            {
                if (!gp.Constants[i].Equals(Constants[i]))
                    return true;//irrelvant predicate - no contradiction
            }
            return Negation == p.Negation;
        }

        public void AddConstant(Constant c)
        {
            Constants.Add(c);
            m_sCachedToString = null;
        }

        public override Predicate Negate()
        {
            if (m_gpNegation == null)
            {
                m_gpNegation = new GroundedPredicate(this);
                m_gpNegation.Negation = !Negation;
                m_gpNegation.m_gpNegation = this;
            }
            return m_gpNegation;
        }

        public override bool IsContainedIn(List<Predicate> lPredicates)
        {
            return lPredicates.Contains(this);
        }

        public override Predicate GenerateKnowGiven(string sTag, bool bKnowWhether)
        {
            GroundedPredicate pKGiven = null;
            if (bKnowWhether)
                pKGiven = new GroundedPredicate("KWGiven" + Name);
            else
                pKGiven = new GroundedPredicate("KGiven" + Name);
            foreach (Constant c in Constants)
                pKGiven.AddConstant(c);
            pKGiven.AddConstant(new Constant(Utilities.TAG, sTag));
            if (!bKnowWhether)
            {
                if (Negation)
                    pKGiven.AddConstant(new Constant(Utilities.VALUE, Utilities.FALSE_VALUE));
                else
                    pKGiven.AddConstant(new Constant(Utilities.VALUE, Utilities.TRUE_VALUE));
            }
            return pKGiven;
        }
        public override Predicate GenerateGiven(string sTag)
        {
            GroundedPredicate pGiven = new GroundedPredicate("Given" + Name);
            foreach (Constant c in Constants)
                pGiven.AddConstant(c);
            pGiven.AddConstant(new Constant(Utilities.TAG, sTag));
            if (Negation)
                return pGiven.Negate();
            return pGiven;
        }

        public override Predicate ToTag()
        {
            GroundedPredicate gpNew = new GroundedPredicate(this);
            if (Negation)
                gpNew.Name = gpNew.Name + "-Remove";
            else
                gpNew.Name = gpNew.Name + "-Add";
            gpNew.Negation = false;

            return gpNew;
        }

        public override int Similarity(Predicate p)
        {
            if (Negation != p.Negation)
                //if (Name != p.Name || Negation != p.Negation)
                return 0;
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                int iSimilarity = 0;
                if (Name == p.Name)
                {
                    for (int i = 0; i < Constants.Count; i++)
                        if (Constants[i].Equals(gpGrounded.Constants[i]))
                            iSimilarity++;
                }
                else
                {
                    foreach (Constant c in Constants)
                        if (gpGrounded.Constants.Contains(c))
                            iSimilarity++;

                }
                return iSimilarity;
            }
            return 0;
        }

        public override bool SameInvariant(Predicate p, Argument aInvariant)
        {
            if (Name != p.Name)
                return false;
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                for (int i = 0; i < Constants.Count; i++)
                {
                    if (Constants[i].Equals(aInvariant)
                        && !gpGrounded.Constants[i].Equals(aInvariant))
                        return false;
                }
                return true;
            }
            return false;
        }

        protected override int ComputeHashCode()
        {
            int iSum = 0;
            foreach (Constant c in Constants)
            {
                iSum += c.GetHashCode();
                iSum *= 1000;
            }
            iSum += m_iName;
            return iSum;
        }

        public override Predicate Clone()
        {
            return new GroundedPredicate(this);
        }
    }
}
