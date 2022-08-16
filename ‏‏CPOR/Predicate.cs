using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace CPOR
{
    public abstract class Predicate : IComparable<Predicate>
    {
        public bool Negation
        {
            get; protected set;
        }

        public bool Cached { get; set; }

        public static bool EnableToStringCaching = true;
        public static int PredicateCount { get; private set; }
        private int m_iHashCode = 0;
        private int m_iID;

        private static List<string> Names = new List<string>();
        protected int m_iName;

        public string Name { get { return Names[m_iName]; } set { SetName(value); } }
        private void SetName(string sName)
        {
            m_iName = Names.IndexOf(sName);
            if (m_iName == -1)
            {
                m_iName = Names.Count;
                Names.Add(sName);
            }
        }



        public Predicate(string sName)
            : this(sName, false)
        {
            if (sName.Contains("take_image_rover0_waypoint5_objective1_camera0_high_res_Option"))
                Debug.Write("*");
        }
        public Predicate(string sName, bool bNegate)
        {
            Name = sName;
            Negation = bNegate;
            m_iID = PredicateCount++;
        }

        /*public Predicate(Predicate original)
        {
            Negation = original.Negation;
            
        }*/

        public abstract bool ConsistentWith(Predicate pState);

        public abstract Predicate Negate();

        public Predicate Canonical()
        {
            if (Negation)
                return Negate();
            else
                return this;
        }

        internal bool IsNegation(Predicate pf)
        {
            Negation = !Negation;
            bool bSame = Equals(pf);
            Negation = !Negation;
            return bSame;
        }

        public abstract bool IsContainedIn(List<Predicate> lPredicates);

        public abstract Predicate GenerateKnowGiven(string sTag, bool bKnowWhether);
        public abstract Predicate GenerateGiven(string sTag);

        public Predicate GenerateKnowGiven(string sTag)
        {
            return GenerateKnowGiven(sTag, false);
        }

        #region IComparable<Predicate> Members

        protected string m_sCachedToString = null;
        public int CompareTo(Predicate other)
        {
            int iResult = ToString().ToLower().CompareTo(other.ToString().ToLower());
            return iResult;
        }

        #endregion

        public override sealed int GetHashCode()
        {
            if (m_iHashCode == 0)
            {
                m_iHashCode = ComputeHashCode() + 1;//offest of 1 to avoid 0 hash code (negtive means negations)
                if (Negation)
                    m_iHashCode *= -1;
            }
            return m_iHashCode;
        }

        protected abstract int ComputeHashCode();
        protected abstract string GetString();

        public override sealed string ToString()
        {
            if (m_sCachedToString == null || !EnableToStringCaching)
                m_sCachedToString = GetString();
            return m_sCachedToString;
        }

        public abstract Predicate ToTag();

        public abstract int Similarity(Predicate p);

        public abstract bool SameInvariant(Predicate p, Argument aInvariant);

        //for MPSR
        public static Predicate GenerateKNot(Constant cTag1, Constant cTag2)
        {
            GroundedPredicate gp = new GroundedPredicate("KNot");
            int iTag1 = int.Parse(cTag1.Name.Substring(3));
            int iTag2 = int.Parse(cTag2.Name.Substring(3));
            if (iTag1 < iTag2)
            {
                gp.AddConstant(cTag1);
                gp.AddConstant(cTag2);
            }
            else
            {
                gp.AddConstant(cTag2);
                gp.AddConstant(cTag1);
            }
            return gp;
        }
        //for SDR
        public static Predicate GenerateKNot(Argument pTag)
        {
            ParametrizedPredicate pp = new ParametrizedPredicate("KNot");
            pp.AddParameter(pTag);
            return pp;
        }

        public abstract Predicate Clone();
    }
}
