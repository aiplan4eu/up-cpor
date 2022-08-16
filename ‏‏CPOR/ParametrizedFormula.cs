using System;
using System.Collections.Generic;
using System.Linq;

namespace CPOR
{
    class ParametrizedFormula : CompoundFormula
    {
        public Dictionary<string, string> Parameters;
        public ParametrizedFormula(string sOperator) : base(sOperator)
        {
            Parameters = new Dictionary<string, string>();
        }

        public ParametrizedFormula(ParametrizedFormula cf)
            : this(cf.Operator)
        {
            Parameters = new Dictionary<string, string>(cf.Parameters);
        }

        public override Formula Negate()
        {
            CompoundFormula cfNegate = new ParametrizedFormula(this);
            foreach (Formula fOperand in Operands)
                cfNegate.AddOperand(fOperand.Negate());
            return cfNegate;
        }
        public override bool ContainsNonDeterministicEffect()
        {
            foreach (Formula fOperand in Operands)
                if (fOperand.ContainsNonDeterministicEffect())
                    return true;
            return false;

        }
        public override List<Predicate> GetNonDeterministicEffects()
        {
            List<Predicate> lNonDetPredicates = new List<Predicate>();
            foreach (Formula f in Operands)
            {
                lNonDetPredicates.AddRange(f.GetNonDeterministicEffects());
            }
            return lNonDetPredicates;
        }

        public override string ToString()
        {
            string s = "(" + Operator + " ";
            foreach (KeyValuePair<string, string> p in Parameters)
            {
                s += "(" + p.Key + " - " + p.Value + ") ";
            }
            s += Parser.ListToString(Operands) + ")";
            return s;
        }
        public override Formula Simplify()
        {
            if (Simplified)
                return this;
            ParametrizedFormula pf = new ParametrizedFormula(this);
            foreach (Formula f in Operands)
                pf.AddOperand(f.Simplify());
            return pf;
        }
        public bool AddOperand(Formula f)
        {
            if (Operands.Count > 0)
                throw new NotImplementedException();
            SimpleAddOperand(f);
            return false;
        }
        public override Formula PartiallyGround(Dictionary<Parameter, Constant> dBindings)
        {
            ParametrizedFormula cfGrounded = new ParametrizedFormula(this);
            foreach (Formula fSub in Operands)
            {
                Formula fGrounded = fSub.PartiallyGround(dBindings);
                cfGrounded.AddOperand(fGrounded);
            }
            return cfGrounded;
        }

        public IEnumerable<Formula> Ground(List<Constant> lConstants)
        {
            if (Parameters.Count > 1)
                throw new NotImplementedException();

            string sParamName = Parameters.Keys.First();
            string sParamType = Parameters.Values.First();
            Parameter pFirst = new Parameter(sParamType, sParamName);

            foreach (Constant c in lConstants)
            {
                if (c.Type == sParamType)
                {
                    Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
                    dBindings[pFirst] = c;
                    foreach (Formula fSub in Operands)
                    {
                        Formula fNew = fSub.PartiallyGround(dBindings);
                        yield return fNew;
                    }
                }
            }
        }

        public override Formula RemoveUniversalQuantifiers(List<Constant> lConstants, List<Predicate> lConstantPredicates, Domain d)
        {
            string sOperator = "";
            if (Operator == "forall")
                sOperator = "and";
            if (Operator == "exists")
                sOperator = "or";
            CompoundFormula fNew = new CompoundFormula(sOperator);
            if (Parameters.Count > 1)
                throw new NotImplementedException();
            string sParamName = Parameters.Keys.First();
            string sParamType = Parameters.Values.First();
            Parameter pFirst = new Parameter(sParamType, sParamName);

            foreach (Constant c in lConstants)
            {
                if (c.Type == sParamType)
                {
                    Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
                    dBindings[pFirst] = c;
                    foreach (Formula fSub in Operands)
                    {
                        Formula fRemoved = fSub.PartiallyGround(dBindings);
                        if (fRemoved == null)
                            continue;
                        Formula fNewSub = fRemoved.RemoveUniversalQuantifiers(lConstants, lConstantPredicates, d);

                        if (fNewSub is PredicateFormula)
                        {
                            Predicate p = ((PredicateFormula)fNewSub).Predicate;
                            if (p == Domain.TRUE_PREDICATE)
                            {
                                if (sOperator == "and")
                                    continue;
                                else if (sOperator == "or")
                                    return fNewSub;
                                else
                                    throw new NotImplementedException();
                            }
                            if (p == Domain.FALSE_PREDICATE)
                            {
                                if (sOperator == "and")
                                    return fNewSub;
                                else if (sOperator == "or")
                                    continue;
                                else
                                    throw new NotImplementedException();
                            }

                        }
                        if (fNewSub != null)
                            fNew.AddOperand(fNewSub);
                    }
                }
            }
            if (fNew.Operands.Count == 0)
            {
                if (sOperator == "and")
                    return new PredicateFormula(Domain.TRUE_PREDICATE);
                if (sOperator == "or" || sOperator == "oneof")
                    return new PredicateFormula(Domain.FALSE_PREDICATE);
            }
            return fNew;
        }

    }
}
