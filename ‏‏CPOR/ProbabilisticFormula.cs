using System;
using System.Collections.Generic;
using System.Linq;

namespace CPOR
{
    public class ProbabilisticFormula : Formula
    {
        public List<Formula> Options { get; private set; }
        public List<double> Probabilities { get; private set; }

        public ProbabilisticFormula()
        {
            Options = new List<Formula>();
            Probabilities = new List<double>();
        }

        public void AddOption(Formula fOption, double dProb)
        {
            Options.Add(fOption);
            Probabilities.Add(dProb);
        }



        public override string ToString()
        {
            string s = "(probabilistic";
            for (int i = 0; i < Options.Count; i++)
            {
                s += " " + Math.Round(Probabilities[i], 3) + " " + Options[i].ToString();
            }
            s += ")";
            return s;
        }

        public override bool IsTrue(IEnumerable<Predicate> lKnown, bool bContainsNegations)
        {
            return false;
        }

        public override bool IsFalse(IEnumerable<Predicate> lKnown, bool bContainsNegations)
        {
            return false;
        }

        public override Formula Ground(Dictionary<Parameter, Constant> dBindings)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Ground(dBindings), Probabilities[i]);
            return pf;
        }

        public override Formula PartiallyGround(Dictionary<Parameter, Constant> dBindings)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].PartiallyGround(dBindings), Probabilities[i]);
            return pf;
        }

        public override Formula Negate()
        {
            throw new NotImplementedException();
        }

        public override void GetAllPredicates(HashSet<Predicate> lPredicates)
        {
            foreach (Formula f in Options)
                f.GetAllPredicates(lPredicates);
        }

        public override void GetAllEffectPredicates(HashSet<Predicate> lConditionalPredicates, HashSet<Predicate> lNonConditionalPredicates)
        {
            foreach (Formula f in Options)
                f.GetAllEffectPredicates(lConditionalPredicates, lNonConditionalPredicates);

        }

        public override bool ContainsCondition()
        {
            foreach (Formula f in Options)
                if (f.ContainsCondition())
                    return true;
            return false;
        }

        public override Formula Clone()
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Clone(), Probabilities[i]);
            return pf;
        }

        public override bool ContainedIn(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            throw new NotImplementedException();
        }

        public override Formula Replace(Formula fOrg, Formula fNew)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Replace(fOrg, fNew), Probabilities[i]);
            return pf;
        }

        public override Formula Replace(Dictionary<Formula, Formula> dTranslations)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Replace(dTranslations), Probabilities[i]);
            return pf;
        }

        public override Formula Simplify()
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Simplify(), Probabilities[i]);
            return pf;
        }

        public override Formula Regress(Action a, IEnumerable<Predicate> lObserved)
        {
            throw new NotImplementedException();
        }

        public override Formula Regress(Action a)
        {
            throw new NotImplementedException();
        }

        public override Formula Reduce(IEnumerable<Predicate> lKnown)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].Reduce(lKnown), Probabilities[i]);
            return pf;
        }

        public override bool ContainsNonDeterministicEffect()
        {
            return true;
        }

        public override int GetMaxNonDeterministicOptions()
        {
            throw new NotImplementedException();
        }

        public override void GetAllOptionalPredicates(HashSet<Predicate> lPredicates)
        {
            foreach (Formula f in Options)
                f.GetAllOptionalPredicates(lPredicates);
        }

        public override Formula CreateRegression(Predicate Predicate, int iChoice)
        {
            throw new NotImplementedException();
        }

        public override Formula GenerateGiven(string sTag, List<string> lAlwaysKnown)
        {
            throw new NotImplementedException();
        }

        public override Formula AddTime(int iTime)
        {
            throw new NotImplementedException();
        }

        public override Formula ReplaceNegativeEffectsInCondition()
        {
            throw new NotImplementedException();
        }

        public override Formula RemoveImpossibleOptions(IEnumerable<Predicate> lObserved)
        {
            throw new NotImplementedException();
        }

        public override Formula ApplyKnown(IEnumerable<Predicate> lKnown)
        {
            throw new NotImplementedException();
        }

        public override List<Predicate> GetNonDeterministicEffects()
        {
            return GetAllPredicates().ToList();
        }

        public override Formula RemoveUniversalQuantifiers(List<Constant> lConstants, List<Predicate> lConstantPredicates, Domain d)
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Options.Count; i++)
                pf.AddOption(Options[i].RemoveUniversalQuantifiers(lConstants, lConstantPredicates, d), Probabilities[i]);
            return pf;
        }

        public override Formula GetKnowledgeFormula(List<string> lAlwaysKnown, bool bKnowWhether)
        {
            throw new NotImplementedException();
        }

        public override Formula ReduceConditions(IEnumerable<Predicate> lKnown)
        {
            throw new NotImplementedException();
        }

        public override Formula RemoveNegations()
        {
            ProbabilisticFormula pf = new ProbabilisticFormula();
            for (int i = 0; i < Probabilities.Count; i++)
            {
                Formula fRemoved = Options[i].RemoveNegations();
                if (fRemoved != null)
                {
                    pf.AddOption(fRemoved, Probabilities[i]);
                }
            }
            return pf;
        }

        public override Formula ToCNF()
        {
            throw new NotImplementedException();
        }

        public override void GetNonDeterministicOptions(List<CompoundFormula> lOptions)
        {
            throw new NotImplementedException();
        }
    }
}
