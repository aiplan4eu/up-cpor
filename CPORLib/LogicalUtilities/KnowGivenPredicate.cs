using CPORLib.Tools;
using System.Collections.Generic;

namespace CPORLib.LogicalUtilities
{
    class KnowGivenPredicate : GroundedPredicate
    {
        public bool KnowWhether { get; private set; }
        public GroundedPredicate Predicate { get; private set; }
        public string Tag { get; private set; }
        public bool Value { get; private set; }
        public KnowGivenPredicate(GroundedPredicate p, bool bValue, string sTag, bool bKnowWhether)
            : base((bKnowWhether ? "KWGiven" : "KGiven") + p.Name)
        {
            KnowWhether = bKnowWhether;
            Predicate = p;
            Tag = sTag;
            Value = bValue;
            Constants = new List<Constant>(p.Constants);
            Constants.Add(new Constant(Utilities.TAG, Tag));
            if (!bKnowWhether)
            {
                if (Value)
                    Constants.Add(new Constant(Utilities.VALUE, Utilities.TRUE_VALUE));
                else
                    Constants.Add(new Constant(Utilities.VALUE, Utilities.FALSE_VALUE));
            }
        }
    }
}
