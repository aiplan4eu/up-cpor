using System.Collections.Generic;

namespace CPORLib.LogicalUtilities
{
    public class PredicateListComparer : IEqualityComparer<List<Predicate>>
    {
        #region IEqualityComparer<List<Predicate>> Members

        public bool Equals(List<Predicate> x, List<Predicate> y)
        {
            if (x.Count != y.Count)
                return false;
            foreach (Predicate p in x)
                if (!y.Contains(p))
                    return false;
            return true;
        }

        public int GetHashCode(List<Predicate> obj)
        {
            int iCode = 0;
            foreach (Predicate p in obj)
                iCode += p.GetHashCode();
            return iCode;
        }

        #endregion
    }
}
