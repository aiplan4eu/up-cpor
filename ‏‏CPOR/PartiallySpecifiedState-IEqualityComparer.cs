using System.Collections.Generic;
using System.Linq;

namespace CPOR
{

    class PartiallySpecifiedState_IEqualityComparer : IEqualityComparer<PartiallySpecifiedState>
    {
        public bool Equals(PartiallySpecifiedState x, PartiallySpecifiedState y)
        {
            if (x.ID == y.ID)
                return true;
            bool ans = x.Equals(y);

            if (ans)
            {
                if (x.regressionFormula != null)
                {
                    for (int i = 0; i < x.regressionFormula.Count; i++)
                    {
                        GroundedPredicate gp = x.regressionFormula.Keys.ElementAt(i);
                        if (x.regressionFormula[gp] == null)
                        {
                            x.regressionFormula[gp] = x.regress(new PredicateFormula(gp), x.countOfActionFromRoot);
                        }
                    }
                }

                if (y.regressionFormula != null)
                {
                    for (int i = 0; i < y.regressionFormula.Count; i++)
                    {
                        GroundedPredicate gp = y.regressionFormula.Keys.ElementAt(i);
                        if (y.regressionFormula[gp] == null)
                        {
                            y.regressionFormula[gp] = y.regress(new PredicateFormula(gp), y.countOfActionFromRoot);
                        }
                    }
                }

                if (x.regressionFormula == null && y.regressionFormula == null)
                    return true;
                if (x.regressionFormula != null && y.regressionFormula == null)
                    return false;
                if (x.regressionFormula == null && y.regressionFormula != null)
                    return false;
                foreach (KeyValuePair<GroundedPredicate, Formula> gf in x.regressionFormula)
                {
                    if (!y.regressionFormula.ContainsKey(gf.Key))
                    {
                        y.regressionFormula.Add(gf.Key, y.regress(new PredicateFormula(gf.Key), y.countOfActionFromRoot));
                    }
                    if (!EqualFormula(y.regressionFormula[gf.Key], (gf.Value)))
                        return false;
                }

                foreach (KeyValuePair<GroundedPredicate, Formula> gf in y.regressionFormula)
                {
                    if (!x.regressionFormula.ContainsKey(gf.Key))
                    {
                        x.regressionFormula.Add(gf.Key, x.regress(new PredicateFormula(gf.Key), x.countOfActionFromRoot));
                    }
                    if (!(EqualFormula(x.regressionFormula[gf.Key], gf.Value)))
                        return false;
                }
                return true;
            }
            if (ans)
                return true;
            return false;
        }

        public bool EqualFormula(Formula f1, Formula f2)
        {
            HashSet<GroundedPredicate> removeSet = new HashSet<GroundedPredicate>();
            List<Predicate> f1Facts = f1.GetAllPredicates().ToList();
            List<Predicate> f2Facts = f2.GetAllPredicates().ToList();
            bool f1ContainRandomVar = false;
            bool f2ContainRandomVar = false;

            foreach (GroundedPredicate gp in f1Facts)
            {
                if (gp.ToString().Contains(Domain.OPTION_PREDICATE))
                {
                    f1ContainRandomVar = true;
                }
                else
                {
                    if (!f2Facts.Contains(gp))
                    {
                        return false;
                    }
                }

            }

            foreach (GroundedPredicate gp in f2Facts)
            {
                if (gp.ToString().Contains(Domain.OPTION_PREDICATE))
                {
                    f2ContainRandomVar = true;
                }
                else
                {
                    if (!f1Facts.Contains(gp))
                    {
                        return false;
                    }
                }

            }
            if (f1ContainRandomVar && f2ContainRandomVar)
                return true;

            if (!f1ContainRandomVar && !f2ContainRandomVar)
                return true;

            return false;
        }
        public int GetHashCode(PartiallySpecifiedState x)
        {
            return 5;// x.GetHashCode();
        }
    }
}
