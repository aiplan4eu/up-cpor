using System;
using System.Collections.Generic;
using System.Text;

namespace CPORLib.LogicalUtilities
{
    public class RegressedPredicate : GroundedPredicate
    {
        public RegressedPredicate Next { get; private set; }
        public int Choice { get; private set; }
        public RegressedPredicate(GroundedPredicate pCurrent, Predicate pNext, int iChoice)
            : base(pCurrent)
        {
            Choice = iChoice;
            if (pNext is RegressedPredicate)
                Next = (RegressedPredicate)pNext;
            else
                Next = null;
        }
        /*
        public RegressedPredicate(GroundedPredicate pCurrent, int iChoice)
            : base(pCurrent.Name)
        {
            Negation = pCurrent.Negation;
            Next = null;
            Choice = iChoice;
        }
         * */
    }
}
