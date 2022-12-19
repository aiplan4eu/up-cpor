
using CPORLib.LogicalUtilities;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
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

        public static readonly Predicate Observed = new GroundedPredicate("observed");


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

        public static string[] SplitString(string sOrg, char[] ac, StringSplitOptions options = StringSplitOptions.None)
        {
            List<string> lStrings = new List<string>();
            string sCurrent = "";
            for(int i = 0; i < sOrg.Length; i++)
            {
                if (ac.Contains(sOrg[i]))
                {
                    if (sCurrent != "" || options != StringSplitOptions.RemoveEmptyEntries)
                    {
                        lStrings.Add(sCurrent);
                    }
                    sCurrent = "";
                }
                else
                    sCurrent += sOrg[i];
            }
            if (sCurrent != "")
                lStrings.Add(sCurrent);

            return lStrings.ToArray();
        }

        public static string Replace(string sOrg, char[] aToReplace, char cReplacement)
        {
            string sResult = "";
            foreach(char c in sOrg)
            {
                if (aToReplace.Contains(c))
                    sResult += cReplacement;
                else
                    sResult += c;
            }
            return sResult;
        }

        public static string[] SplitString(string sOrg, char c, StringSplitOptions options = StringSplitOptions.None)
        {
            List<string> lStrings = new List<string>();
            string sCurrent = "";
            for (int i = 0; i < sOrg.Length; i++)
            {
                if (sOrg[i] == c)
                {
                    if (sCurrent != "" || options != StringSplitOptions.RemoveEmptyEntries)
                    {
                        lStrings.Add(sCurrent);
                    }
                    sCurrent = "";
                }
                else
                    sCurrent += sOrg[i];
            }
            if (sCurrent != "")
                lStrings.Add(sCurrent);

            

            return lStrings.ToArray();
        }

    }
}
