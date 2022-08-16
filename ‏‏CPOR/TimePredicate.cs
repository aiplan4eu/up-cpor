using System;
using System.Collections.Generic;

namespace CPOR
{
    class TimePredicate : Predicate
    {
        public int Time { get; private set; }
        public Predicate Predicate { get; private set; }
        public TimePredicate(Predicate p, int iTime)
            : base(p.Name + "-" + iTime)
        {
            Predicate = p;
            Negation = p.Negation;
            Time = iTime;
        }

        public override bool ConsistentWith(Predicate pState)
        {
            if (pState is TimePredicate)
                return Predicate.ConsistentWith(((TimePredicate)pState).Predicate);
            return Predicate.ConsistentWith(pState);
        }

        public override Predicate Negate()
        {
            TimePredicate tpNegate = new TimePredicate(Predicate.Negate(), Time);
            return tpNegate;
        }

        public override bool IsContainedIn(List<Predicate> lPredicates)
        {
            return Predicate.IsContainedIn(lPredicates);
        }

        public override Predicate GenerateKnowGiven(string sTag, bool bKnowWhether)
        {
            return Predicate.GenerateKnowGiven(sTag, bKnowWhether);
        }

        public override Predicate GenerateGiven(string sTag)
        {
            return Predicate.GenerateGiven(sTag);
        }

        protected override string GetString()
        {
            return Predicate.ToString().Replace(Predicate.Name, Predicate.Name + "-" + Time);
        }

        public override bool Equals(object obj)
        {
            if (obj is TimePredicate)
            {
                TimePredicate tp = (TimePredicate)obj;
                if (tp.Time == Time)
                    return tp.Predicate.Equals(Predicate);
                return false;
            }
            return false;
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
