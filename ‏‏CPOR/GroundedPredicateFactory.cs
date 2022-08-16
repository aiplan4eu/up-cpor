using System.Collections.Generic;

namespace CPOR
{
    public class GroundedPredicateFactory
    {
        private static Dictionary<string, GroundedPredicate> AllGrounded = new Dictionary<string, GroundedPredicate>();

        public static GroundedPredicate Get(string sName, List<Argument> lParameters, Dictionary<Parameter, Constant> dBindings, bool bNegation)
        {
            string sFullName = GetString(sName, lParameters, dBindings, bNegation);
            if (sFullName == null)
                return null;
            GroundedPredicate gp = null;
            if (AllGrounded.TryGetValue(sFullName, out gp))
                return gp;
            return null;
        }

        private static string GetString(string sName, List<Argument> lParameters, Dictionary<Parameter, Constant> dBindings, bool bNegation)
        {
            string sFullName = "";
            if (bNegation)
                sFullName = "~";
            sFullName += sName;
            foreach (Argument a in lParameters)
            {
                if (a is Parameter p)
                {
                    if (!dBindings.ContainsKey(p))
                        return null;
                    sFullName += " " + dBindings[p];
                }
                else
                    sFullName += " " + a.Name;
            }
            return sFullName;
        }

        public static void Add(string sName, List<Argument> lParameters, Dictionary<Parameter, Constant> dBindings, GroundedPredicate gp, bool bNegation)
        {
            string sFullName = GetString(sName, lParameters, dBindings, bNegation);
            string sNotFullName = GetString(sName, lParameters, dBindings, !bNegation);
            gp.Cached = true;
            AllGrounded[sFullName] = gp;
            GroundedPredicate gpNot = (GroundedPredicate)gp.Negate();
            gpNot.Cached = true;
            AllGrounded[sNotFullName] = gpNot;
        }
    }
}
