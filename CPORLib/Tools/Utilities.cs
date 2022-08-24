
using CPORLib.LogicalUtilities;
using System.Collections;
using System.Collections.Generic;
using System.Text;

namespace CPORLib.Tools
{
    public class Utilities
    {
        public const string OPTION = "OPTION_TYPE";
        public const string OPTION_PREDICATE = "option";
        public const string VALUE = "VALUE_TYPE";
        public const string VALUE_PARAMETER = "?V_PARAM";
        public const string TAG = "TAG_TYPE";
        public const string TAG_PARAMETER = "?TAG_PARAM";
        public const string TRUE_VALUE = "V_TRUE";
        public const string FALSE_VALUE = "V_FALSE";
        public const string TRUE_PREDICATE_NAME = "P_TRUE";
        public const string FALSE_PREDICATE_NAME = "P_FALSE";

        public const string DELIMITER_CHAR = "~";


        public static readonly GroundedPredicate TRUE_PREDICATE = new GroundedPredicate(TRUE_PREDICATE_NAME);
        public static readonly GroundedPredicate FALSE_PREDICATE = new GroundedPredicate(FALSE_PREDICATE_NAME);



        public static bool SameList(List<string> l1, List<string> l2)
        {
            if (l1 == null && l2 == null)
                return true;
            if (l1 == null && l2 != null)
                return false;
            if (l1 != null && l2 == null)
                return false;

            if (l1.Count != l2.Count)
                return false;
            for (int i = 0; i < l1.Count; i++)
                if (l1[i] != l2[i])
                    return false;
            return true;
        }
        public static string ListToString(IList l)
        {
            if (l.Count == 0)
                return "";
            string s = "";
            for (int i = 0; i < l.Count - 1; i++)
            {
                s += l[i].ToString() + " ";
            }
            s += l[l.Count - 1] + "";
            return s;
        }

        public static string ListToString(IList l, int cTabs)
        {
            if (l.Count == 0)
                return "";
            string s = "";
            for (int i = 0; i < l.Count - 1; i++)
            {
                if (l[i] is CompoundFormula)
                    s += ((CompoundFormula)l[i]).ToString(cTabs);
                else
                    s += l[i].ToString() + " ";
            }
            if (l[l.Count - 1] is CompoundFormula)
                s += ((CompoundFormula)l[l.Count - 1]).ToString(cTabs) + "";
            else
                s += l[l.Count - 1] + "";
            return s;
        }


    }
}
