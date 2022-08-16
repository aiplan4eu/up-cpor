using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace CPOR
{
    public class CompoundFormula : Formula
    {
        public string Operator { get; private set; }
        public List<Formula> Operands { get; private set; }
        public bool Simplified { get; private set; }
        public List<List<int>> SATSolverClauses { get; private set; }
        public CompoundFormula(string sOperator) : base()
        {
            Operator = sOperator;
            Operands = new List<Formula>();
            Simplified = false;
            Size = 0;
            SATSolverClauses = new List<List<int>>();
        }

        public CompoundFormula(CompoundFormula cf) : this(cf.Operator)
        {
            foreach (Formula f in cf.Operands)
                AddOperand(f);
            Simplified = cf.Simplified;
            Size = 0;
            SATSolverClauses = new List<List<int>>();
        }

        public void AddSATSolverClause(List<int> lClause)
        {
            SATSolverClauses.Add(lClause);
        }

        public bool IsSimpleFormula()
        {
            foreach (Formula f in Operands)
                if (f is CompoundFormula)
                    return false;
            return true;
        }
        /*
        public void SimpleAddOperand(Formula f)
        {
            Operands.Add(f);
        }
        */
        public void SimpleAddOperand(Formula f)
        {
            m_sCachedToString = null;
            if (f == null)
                return;

            if (f is ParametrizedFormula)//for universal quantifiers, assuming for now that they were not added before
            {
                Size += f.Size;
                Operands.Add(f);
                return;
            }

            if (f is CompoundFormula && ((CompoundFormula)f).Operator == Operator)
            {
                bool bContainsAll = true;
                foreach (Formula fOperand in ((CompoundFormula)f).Operands)
                {
                    Size += fOperand.Size;
                    SimpleAddOperand(fOperand);
                }
                return;
            }
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operands.Count == 1)
                {
                    Size += cf.Operands[0].Size;
                    AddOperand(cf.Operands[0]);
                    return;
                }
            }
            Size += f.Size;
            Simplified = false;
            Operands.Add(f);
        }
        public void SimpleAddOperand(Predicate p)
        {
            PredicateFormula pf = new PredicateFormula(p);
            SimpleAddOperand(pf);
        }

        //returns true if operand already exists
        public bool AddOperand(Formula f)
        {
            if (f == null)
                throw new ArgumentNullException();

            m_sCachedToString = null;
            if (f == null)
                return false;
            if (Size > 20 || f.Size > 20)
            {
                SimpleAddOperand(f);
                return false;
            }
            if (Operator == "when")
            {
                if (Operands.Count < 2)
                {
                    Operands.Add(f);
                    Size += f.Size;
                }
                else
                    throw new NotImplementedException();
                return false;
            }
            if (Operands.Contains(f))
                return true;
            if (f is ParametrizedFormula)//for universal quantifiers, assuming for now that they were not added before
            {
                Operands.Add(f);
                Size += f.Size;
                return false;
            }
            if (f is ProbabilisticFormula)
            {
                Operands.Add(f);
                Size += f.Size;
                return false;
            }
            if (f is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)f).Predicate;
                if (p == Domain.TRUE_PREDICATE)
                    if (Operator == "and")
                        return false;
                if (p == Domain.FALSE_PREDICATE)
                    if (Operator == "or")
                        return false;
            }
            if (f is CompoundFormula && ((CompoundFormula)f).Operator == Operator)
            {
                bool bContainsAll = true;
                foreach (Formula fOperand in ((CompoundFormula)f).Operands)
                {
                    if (!AddOperand(fOperand))
                        bContainsAll = false;
                    else
                        Size += fOperand.Size;
                }
                return bContainsAll;
            }
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operands.Count == 1)
                {
                    Size += cf.Operands[0].Size;
                    return AddOperand(cf.Operands[0]);
                }
            }
            Simplified = false;
            if (f is CompoundFormula && ((CompoundFormula)f).Operator == "oneof")
            {
                Size += f.Size;
                Operands.Add(f);//don't know how to negate oneof for now
                return false;
            }
            else
            {

                if (Operator != "oneof" && Operands.Contains(f.Negate()))
                {
                    if (Operator == "and")
                        Operands.Add(new PredicateFormula(Domain.FALSE_PREDICATE));
                    else if (Operator == "or")
                        Operands.Add(new PredicateFormula(Domain.TRUE_PREDICATE));
                    else
                        throw new NotImplementedException();
                    Operands.Remove(f.Negate());
                    return true;
                }
                else
                {
                    Size += f.Size;
                    Operands.Add(f);
                    return false;
                }
            }
            return true;
        }
        public bool AddOperand(Predicate p)
        {
            if (p == null)
                throw new ArgumentNullException();
            PredicateFormula pf = new PredicateFormula(p);
            return AddOperand(pf);

        }
        public override bool IsTrue(IEnumerable<Predicate> lKnown, bool bContainsNegations)
        {
            bool bValue = false;
            int cCountTrue = 0, cCountFalse = 0;
            foreach (Formula f in Operands)
            {
                bValue = f.IsTrue(lKnown, bContainsNegations);
                if (bValue)
                    cCountTrue++;
                if (Operator == "and" && !bValue)
                    return false;
                else if (Operator == "or" && bValue)
                    return true;
                else if (Operator == "oneof")
                {
                    if (cCountTrue > 1)
                        return false;
                    if (f.IsFalse(lKnown, bContainsNegations))
                        cCountFalse++;
                }
            }
            if (Operator == "oneof")
                return cCountFalse + cCountTrue == Operands.Count;
            return Operator == "and";
        }
        public override bool IsFalse(IEnumerable<Predicate> lKnown, bool bContainsNegations)
        {
            bool bValue = false;
            int cCountTrue = 0, cCountFalse = 0;
            foreach (Formula f in Operands)
            {
                bValue = f.IsFalse(lKnown, bContainsNegations);
                if (bValue)
                    cCountFalse++;
                if (Operator == "and" && bValue)
                    return true;
                else if (Operator == "or")
                {
                    if (f.IsTrue(lKnown, bContainsNegations))
                        return false;
                }
                else if (Operator == "oneof")
                {
                    if (f.IsTrue(lKnown, bContainsNegations))
                        cCountTrue++;
                    if (cCountTrue > 1)
                        return true;
                }
            }
            //need to take care of duplicate operands in oneof statements
            if (Operator == "oneof" && cCountFalse + cCountTrue == Operands.Count)
                return cCountTrue == 0;
            if (Operator == "or" && cCountFalse == Operands.Count)
                return true;
            return false;
        }
        private string m_sCachedToString = null;
        public override string ToString()
        {
            //return "(" + Operator + " " + Parser.ListToString(Operands) + ")";
            if (m_sCachedToString == null)
                m_sCachedToString = ToString(0);
            return m_sCachedToString;
        }


        public string ToString(int cTabs)
        {
            string s = "\n";
            for (int i = 0; i < cTabs; i++)
                s += "\t";
            s += "(" + Operator + " " + Parser.ListToString(Operands, cTabs + 1) + ")";
            return s;
        }


        public override Formula Negate()
        {
            CompoundFormula cfNegate = null;
            if (Operator == "when")
                return this;//special case - "when" is not truly a boolean formula (?)
            if (Operator == "or")
                cfNegate = new CompoundFormula("and");
            if (Operator == "and")
                cfNegate = new CompoundFormula("or");
            if (Operator == "oneof")
                throw new NotImplementedException("Not handling oneof for now");
            if (Operator == "not")
                return Operands[0];
            if (cfNegate == null)
                return null;
            foreach (Formula fOperand in Operands)
                cfNegate.AddOperand(fOperand.Negate());
            return cfNegate;
        }


        public override Formula Reduce(IEnumerable<Predicate> lKnown)
        {
            CompoundFormula cfReduced = new CompoundFormula(Operator);
            Formula fNew = null;
            foreach (Formula f in Operands)
            {
                bool bTrue = false;
                bool bFalse = false;
                if (f is PredicateFormula)
                {
                    fNew = null;
                    Predicate p = ((PredicateFormula)f).Predicate;
                    if (lKnown.Contains(p))
                        bTrue = true;
                    else if (lKnown.Contains(p.Negate()))
                        bFalse = true;
                    else
                        fNew = f;
                }
                else
                    fNew = ((CompoundFormula)f).Reduce(lKnown);
                //if (fNew.IsTrue(lKnown))
                if (bTrue || (!bFalse && fNew.IsTrue(null)))
                {
                    if (Operator == "or")
                        return new PredicateFormula(Domain.TRUE_PREDICATE);//reasoning predicate no longer informative
                                                                           //else if (Operator == "and")
                                                                           //   cfReduced.Operands.Remove(fNew); - not adding so no need to remove
                    else if (Operator == "oneof")
                    {//(oneof a b c) and a = (and !b !c)
                        cfReduced = new CompoundFormula("and");
                        List<Formula> lPredicates = new List<Formula>();
                        foreach (Formula pOther in Operands)
                        {
                            if (!pOther.Equals(f))
                                lPredicates.Add(pOther.Negate());
                        }
                        if (lPredicates.Count == 1)
                            return lPredicates[0];

                        cfReduced.Operands = lPredicates;
                        return cfReduced;
                    }
                    //else
                    //    throw new NotImplementedException();
                }
                //else if (fNew.IsFalse(lKnown))

                else if (bFalse || (!bTrue && fNew.IsFalse(null)))
                {
                    if (Operator == "and")
                    {
                        return new PredicateFormula(Domain.FALSE_PREDICATE);//formula must be false
                    }
                    /* not adding so no need to remove
                else if (Operator == "or")
                {
                    cfReduced.Operands.Remove(fNew);
                }
                else if (Operator == "oneof")
                {
                    cfReduced.Operands.Remove(fNew);
                }
                     * */
                    //else
                    //    throw new NotImplementedException();
                }
                else
                {
                    bool bOperandExists = cfReduced.AddOperand(fNew);
                    if (bOperandExists && Operator == "oneof")
                        return new PredicateFormula(Domain.FALSE_PREDICATE);//oneof requires only one - duplicate means trouble
                }

            }
            if (cfReduced.Operands.Count == 0)
            {
                if (Operator == "and")
                    return new PredicateFormula(Domain.TRUE_PREDICATE);//no negative found so total value is true
                if (Operator == "or")
                    return new PredicateFormula(Domain.FALSE_PREDICATE);//no positive found so total value is false
            }
            if (cfReduced.Operands.Count == 1)
                return cfReduced.Operands[0];
            if (Operator == "and")
                return cfReduced.ReduceAnd();
            if (cfReduced.Operands.Count == 1)
                return cfReduced.Operands[0];
            return cfReduced;
            //return cfReduced.Simplify(); not sure why we would need to simplify here?
        }

        private Formula ReduceAnd()
        {
            List<Predicate> lObligatory = new List<Predicate>();
            foreach (Formula f in Operands)
            {
                if (f is PredicateFormula)
                    lObligatory.Add(((PredicateFormula)f).Predicate);
            }
            if (lObligatory.Count == 0)
                return this;
            CompoundFormula cfAnd = new CompoundFormula("and");
            foreach (Formula f in Operands)
            {
                if (f is PredicateFormula)
                    cfAnd.AddOperand(f);
                else
                {
                    CompoundFormula cf = (CompoundFormula)f;
                    Formula fReduce = cf.Reduce(lObligatory);
                    if (fReduce is PredicateFormula)
                    {
                        if (((PredicateFormula)fReduce).Predicate == Domain.FALSE_PREDICATE)
                            return fReduce;
                        else if (((PredicateFormula)fReduce).Predicate != Domain.TRUE_PREDICATE)
                            cfAnd.AddOperand(fReduce);
                    }
                    else
                        cfAnd.AddOperand(fReduce);
                }
            }
            return cfAnd;
        }

        public override Formula Ground(Dictionary<Parameter, Constant> dBindings)
        {
            CompoundFormula cfGrounded = new CompoundFormula(Operator);
            foreach (Formula fSub in Operands)
            {
                Formula fGrounded = fSub.Ground(dBindings);
                cfGrounded.AddOperand(fGrounded);
            }
            return cfGrounded;
        }

        public override Formula PartiallyGround(Dictionary<Parameter, Constant> dBindings)
        {
            CompoundFormula cfGrounded = new CompoundFormula(Operator);
            foreach (Formula fSub in Operands)
            {
                Formula fGrounded = fSub.PartiallyGround(dBindings);
                if (fGrounded is PredicateFormula)
                {
                    Predicate p = ((PredicateFormula)fGrounded).Predicate;
                    if (p == Domain.TRUE_PREDICATE)
                    {
                        if (Operator == "and")
                            continue;
                        else if (Operator == "or")
                            return fGrounded;
                        else
                            throw new NotImplementedException();
                    }
                    if (p == Domain.FALSE_PREDICATE)
                    {
                        if (Operator == "and")
                            return fGrounded;
                        else if (Operator == "or")
                            continue;
                        else if (Operator == "when")
                        {
                            return null;
                        }
                        else
                            throw new NotImplementedException();
                    }

                }
                cfGrounded.AddOperand(fGrounded);
                if (cfGrounded.IsFalse(null))
                    return new PredicateFormula(Domain.FALSE_PREDICATE);
            }
            return cfGrounded;
        }


        public override void GetAllPredicates(HashSet<Predicate> lPredicates)
        {
            foreach (Formula f in Operands)
                f.GetAllPredicates(lPredicates);
        }
        public override void GetAllEffectPredicates(HashSet<Predicate> lConditionalPredicates, HashSet<Predicate> lNonConditionalPredicates)
        {
            if (Operator == "when")
                Operands[1].GetAllPredicates(lConditionalPredicates);
            else
            {
                foreach (Formula f in Operands)
                {
                    f.GetAllEffectPredicates(lConditionalPredicates, lNonConditionalPredicates);
                }
            }
        }


        public override bool ContainsCondition()
        {
            if (Operator == "when")
                return true;
            foreach (Formula fSub in Operands)
            {
                if (fSub.ContainsCondition())
                    return true;
            }
            return false;
        }

        public override Formula Clone()
        {
            CompoundFormula cfClone = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                cfClone.SimpleAddOperand(f.Clone());
            return cfClone;
        }

        public override bool ContainedIn(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            bool bSuccess = false;
            foreach (Formula fSub in Operands)
            {
                bSuccess = fSub.ContainedIn(lPredicates, bContainsNegations);
                if (Operator == "not")
                    throw new NotImplementedException("Need to implement behavior for not operator");
                if (Operator == "and" && !bSuccess)
                    return false;
                if (Operator == "or" && bSuccess)
                    return true;
            }
            return Operator == "and";
        }

        public bool ConditionDeletesPrecondition()
        {
            Formula fRest = null;
            return ConditionDeletesPrecondition(out fRest);
        }

        private bool ConditionDeletesPrecondition(out Formula fRest)
        {
            //BUGBUG: simplified and not full implementation
            fRest = null;
            if (Operator != "when")
                return false;
            Formula fPre = Operands[0];
            Formula fDelete = fPre.Negate().Simplify();
            bool bFound = false;
            CompoundFormula cfRest = new CompoundFormula("and");
            if (Operands[1] is CompoundFormula)
            {
                foreach (Formula f in ((CompoundFormula)Operands[1]).Operands)
                {
                    if (f.Equals(fDelete))
                        bFound = true;
                    else
                        cfRest.AddOperand(f);
                }
            }
            else
            {
                PredicateFormula f = (PredicateFormula)Operands[1];
                if (f.Equals(fDelete))
                    bFound = true;
                else
                    cfRest.AddOperand(f);
            }
            if (!bFound)
                return false;
            if (cfRest.Operands.Count == 1)
                fRest = cfRest.Operands[0];
            else
                fRest = cfRest;
            return true;
        }

        public CompoundFormula ApplyConditions(Dictionary<Formula, List<Predicate>> dTranslations)
        {
            return (CompoundFormula)AddRemoveConditionalEffects(dTranslations).Simplify();
        }

        public CompoundFormula ApplyConditionsII(List<CompoundFormula> lConditions)
        {
            Dictionary<Formula, Formula> dTranslations = new Dictionary<Formula, Formula>();
            foreach (CompoundFormula cfCondition in lConditions)
            {
                Formula fRest = null;
                if (cfCondition.ConditionDeletesPrecondition(out fRest))
                    dTranslations[cfCondition.Operands[0].Simplify()] = fRest;
                else
                {
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    cfAnd.AddOperand(cfCondition.Operands[0].Simplify());
                    cfAnd.AddOperand(cfCondition.Operands[1].Simplify());
                    dTranslations[cfCondition.Operands[0].Simplify()] = cfAnd.Simplify();
                }
            }
            if (dTranslations.Count == 0)
                return this;
            return (CompoundFormula)Replace(dTranslations);
        }


        //given f->g replace f everywhere with (~f or f and g)
        //possible problem - results in always true statements. When previous formula was f1 xor f2, and f1 was replaced, now the f1 revision is always true and f2 must be false
        private CompoundFormula ApplyConditionII(CompoundFormula cfCondition)
        {
            Formula fPremise = cfCondition.Operands[0];
            CompoundFormula cfConclusion = new CompoundFormula("and");
            cfConclusion.AddOperand(cfCondition.Operands[0]);
            cfConclusion.AddOperand(cfCondition.Operands[1]);
            Formula fNegatePremise = fPremise.Negate();
            CompoundFormula cfOr = new CompoundFormula("or");
            cfOr.AddOperand(fNegatePremise);
            cfOr.AddOperand(cfConclusion.Simplify());
            return (CompoundFormula)Replace(fPremise, cfOr);
        }
        //given f->g replacing f with (f and g)
        private CompoundFormula ApplyCondition(CompoundFormula cfCondition)
        {
            Formula fPremise = cfCondition.Operands[0];
            CompoundFormula cfConclusion = new CompoundFormula("and");
            cfConclusion.AddOperand(cfCondition.Operands[0]);
            cfConclusion.AddOperand(cfCondition.Operands[1]);
            return (CompoundFormula)Replace(fPremise, cfConclusion.Simplify());
        }

        public override Formula Replace(Formula fOrg, Formula fNew)
        {
            if (this.Equals(fOrg))
                return fNew;
            CompoundFormula fReplaced = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                fReplaced.AddOperand(f.Replace(fOrg, fNew));
            return fReplaced;
        }
        public override Formula Replace(Dictionary<Formula, Formula> dTranslations)
        {
            if (dTranslations.ContainsKey(this))
                return dTranslations[this];
            CompoundFormula fReplaced = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                fReplaced.AddOperand(f.Replace(dTranslations));
            return fReplaced;
        }

        public bool IsSimpleConjunction()
        {
            if (Operator != "and")
                return false;
            foreach (Formula f in Operands)
            {
                if (f is CompoundFormula)
                    return false;
            }
            return true;
        }
        // for every f->g replace f with g
        public CompoundFormula AddRemoveConditionalEffects(Dictionary<Formula, List<Predicate>> dEffects)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            if (Operator == "and") //bugbug - not updating more complex structures for now
            {
                List<Formula> lReplaceKeys = new List<Formula>();
                List<Formula> lReplaceNegates = new List<Formula>();
                foreach (Formula fOperand in Operands)
                {
                    if (dEffects.ContainsKey(fOperand))
                    {
                        lReplaceKeys.Add(fOperand);
                    }
                }

                if (lReplaceKeys.Count == 0 && lReplaceNegates.Count == 0)
                    return this;

                List<Predicate> lEffects = new List<Predicate>();
                foreach (Formula fReplace in lReplaceKeys)
                {
                    lEffects.AddRange(dEffects[fReplace]);
                }
                foreach (Formula fOperand in Operands)
                {
                    if (fOperand is PredicateFormula)
                    {
                        PredicateFormula pf = (PredicateFormula)fOperand;
                        if (!lReplaceNegates.Contains(fOperand))
                        {
                            if (!lEffects.Contains(pf.Predicate))
                            {
                                if (!lEffects.Contains(pf.Predicate.Negate()))
                                    cfNew.AddOperand(fOperand);
                            }
                        }
                    }
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)fOperand;
                        CompoundFormula cfRevised = cf.AddRemoveConditionalEffects(dEffects);
                        cfNew.AddOperand(cfRevised);
                    }
                }
                foreach (Predicate p in lEffects)
                    cfNew.AddOperand(new PredicateFormula(p));
            }
            else
            {
                foreach (Formula fOperand in Operands)
                {
                    if (fOperand is PredicateFormula)
                    {
                        bool bContainsKey = dEffects.ContainsKey(fOperand);
                        Formula fNegate = fOperand.Negate();
                        bool bContainsNegate = dEffects.ContainsKey(fNegate);
                        if (bContainsKey || bContainsNegate)
                        {
                            CompoundFormula cfAnd = new CompoundFormula("and");

                            List<Predicate> lEffects = null;
                            if (bContainsKey)
                                lEffects = dEffects[fOperand];
                            if (bContainsNegate)
                                lEffects = dEffects[fNegate];
                            if (!lEffects.Contains(((PredicateFormula)fOperand).Predicate.Negate()))
                                cfAnd.AddOperand(fOperand);
                            foreach (Predicate p in lEffects)
                            {
                                cfAnd.AddOperand(new PredicateFormula(p));
                            }
                            if (bContainsNegate)
                                cfAnd = (CompoundFormula)cfAnd.Negate();
                            cfNew.AddOperand(cfAnd);
                        }
                        else
                            cfNew.AddOperand(fOperand);
                    }
                    else
                        cfNew.AddOperand(((CompoundFormula)fOperand).AddRemoveConditionalEffects(dEffects));
                }
            }
            return cfNew;
        }

        public CompoundFormula RemovePredicates(IEnumerable<Predicate> lPredicates)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
            {
                if (f is PredicateFormula)
                {
                    if (!lPredicates.Contains(((PredicateFormula)f).Predicate))
                        cfNew.SimpleAddOperand(f);
                }
                else
                    cfNew.SimpleAddOperand(((CompoundFormula)f).RemovePredicates(lPredicates));
            }
            return cfNew;
        }

        private bool IsSimpleAnd(Formula f)
        {
            if (f is PredicateFormula)
                return true;
            if (f is ProbabilisticFormula)
                return false;
            CompoundFormula cf = (CompoundFormula)f;
            if (cf.Operator != "and")
                return false;
            foreach (Formula fSub in cf.Operands)
                if (!(fSub is PredicateFormula))
                    return false;
            return true;
        }

        public override Formula Simplify()
        {
            Formula fSimplified = null;
            if (Simplified)
                return this;
            if (Operator == "not")
                fSimplified = Negate();
            if (Operands.Count == 1)
                fSimplified = Operands[0].Simplify();
            if (Operator == "when")
            {
                CompoundFormula cfNew = new CompoundFormula(Operator);
                Formula fFirst = Operands[0].Simplify();
                Formula fSecond = Operands[1].Simplify();

                cfNew.SimpleAddOperand(fFirst);

                if (IsSimpleAnd(fFirst) && IsSimpleAnd(fSecond))
                {
                    HashSet<Predicate> lFirst = fFirst.GetAllPredicates();
                    HashSet<Predicate> lSecond = fSecond.GetAllPredicates();
                    CompoundFormula cfSecond = new CompoundFormula("and");
                    foreach (Predicate p in lSecond)
                        if (!lFirst.Contains(p))
                            cfSecond.AddOperand(p);
                    cfNew.SimpleAddOperand(cfSecond);
                }
                else
                {
                    cfNew.SimpleAddOperand(fSecond);
                }
                cfNew.Simplified = true;
                fSimplified = cfNew;
            }
            else if (Operator == "and" || Operator == "or" || Operator == "oneof")
            {
                /*
                if (Operands.Count == 0)
                {
                    if (Operator == "and")
                        return new PredicateFormula(Domain.TRUE_PREDICATE);
                    if (Operator == "or" || Operator == "oneof")
                        return new PredicateFormula(Domain.FALSE_PREDICATE);
                }
                 * */
                CompoundFormula cfNew = new CompoundFormula(Operator);
                foreach (Formula f in Operands)
                {
                    Formula fSimplify = f.Simplify();
                    if (fSimplify is CompoundFormula)
                    {
                        CompoundFormula cf = (CompoundFormula)fSimplify;
                        if (cf.Operator == Operator)
                        {
                            foreach (Formula ff in cf.Operands)
                                cfNew.AddOperand(ff);
                        }
                        else
                            cfNew.AddOperand(cf);
                    }
                    else if (fSimplify is ProbabilisticFormula)
                    {
                        cfNew.AddOperand(fSimplify);
                    }
                    else
                    {
                        Predicate p = ((PredicateFormula)fSimplify).Predicate;
                        if (p == Domain.TRUE_PREDICATE)
                        {
                            if (Operator == "or")
                                return fSimplify;
                        }
                        else if (p == Domain.FALSE_PREDICATE)
                        {
                            if (Operator == "and")
                                return fSimplify;
                        }
                        else
                            cfNew.AddOperand(fSimplify);
                    }
                }
                if (cfNew.Operands.Count == 1)
                    return cfNew.Operands[0];
                if (cfNew.Operator == "or")
                    cfNew = cfNew.RemoveRedundancies();
                fSimplified = cfNew;
            }
            if (fSimplified is CompoundFormula)
                ((CompoundFormula)fSimplified).Simplified = true;
            return fSimplified;
        }

        private CompoundFormula RemoveRedundancies()
        {
            if (Operator == "or")
            {
                HashSet<Predicate> lPredicates = GetAllPredicates();
                HashSet<Predicate> lObligatory = new HashSet<Predicate>();
                foreach (Predicate p in lPredicates)
                {
                    List<Predicate> lNotP = new List<Predicate>();
                    lNotP.Add(p.Negate());
                    if (IsFalse(lNotP))
                        lObligatory.Add(p);
                }
                if (lObligatory.Count == 0)
                {
                    return this;
                }
                CompoundFormula cfAnd = new CompoundFormula("and");
                CompoundFormula cfOr = new CompoundFormula("or");
                foreach (Predicate p in lObligatory)
                    cfAnd.AddOperand(p);
                foreach (Formula f in Operands)
                    cfOr.AddOperand(f.Reduce(lObligatory));
                cfAnd.AddOperand(cfOr);
                return cfAnd;
            }
            return this;
        }

        public override bool Equals(object obj)
        {
            if (obj is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)obj;
                if (Operator != cf.Operator)
                    return false;
                if (Operands.Count != cf.Operands.Count)
                    return false;
                foreach (Formula f in cf.Operands)
                    if (!Operands.Contains(f))
                        return false;
                return true;
            }
            return false;
        }

        public CompoundFormula ToSimpleForm()
        {
            if (Operator == "and" || Operator == "or" || Operator == "not")
                throw new NotImplementedException();
            if (Operator == "oneof")
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                foreach (Formula fOperand in Operands)
                {
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    foreach (Formula fOther in Operands)
                    {
                        if (fOperand == fOther)
                            cfAnd.AddOperand(fOperand);
                        else
                            cfAnd.AddOperand(fOther.Negate());
                    }
                    cfOr.AddOperand(cfAnd);
                }
                return cfOr;
            }
            return null;
        }

        public override Formula Regress(Action a, IEnumerable<Predicate> lObserved)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
            {
                //Formula fRgressed = f.Regress(a, lObserved);
                Formula fRgressed = f.Regress(a, lObserved);
                //what happens if we get  "TRUE" or "FALSE"?
                cfNew.AddOperand(fRgressed);
            }
            return cfNew.Simplify();
        }

        public override Formula Regress(Action a)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
            {
                //Formula fRgressed = f.Regress(a, lObserved);
                Formula fRgressed = f.Regress(a);
                //what happens if we get  "TRUE" or "FALSE"?
                cfNew.AddOperand(fRgressed);
            }
            return cfNew.Simplify();
        }

        public bool IsSimpleDisjunction()
        {
            if (Operator != "or")
                return false;
            foreach (Formula f in Operands)
                if (f is CompoundFormula)
                    return false;
            return true;
        }

        private bool IsCNF()
        {
            if (Operator != "and")
                return false;
            foreach (Formula f in Operands)
            {
                if (f is CompoundFormula)
                {
                    CompoundFormula cf = (CompoundFormula)f;
                    if (!cf.IsSimpleDisjunction() && !cf.IsSimpleOneOf())
                        return false;
                }
            }
            return true;
        }
        /*
                public List<CompoundFormula> ToCNF()
                {
                    List<CompoundFormula> lClauses = new List<CompoundFormula>();
                    if (Operator == "or")
                    {
                        List<CompoundFormula> lCompoundOperands = new List<CompoundFormula>();
                        List<PredicateFormula> lPredicateOperands = new List<PredicateFormula>();
                        foreach (Formula f in Operands)
                        {
                            if (f is CompoundFormula)
                                lCompoundOperands.Add((CompoundFormula)f);
                            else
                                lPredicateOperands.Add((PredicateFormula)f);
                        }
                        if (lCompoundOperands.Count == 0)
                        {
                            lClauses.Add(this);
                        }
                        else if (lCompoundOperands.Count == 1)
                        {
                            CompoundFormula cfAnd = lCompoundOperands[0];
                            if (cfAnd.Operator != "and")
                                throw new NotImplementedException();
                            foreach (Formula f in cfAnd.Operands)
                            {
                                if (f is PredicateFormula)
                                {
                                    PredicateFormula pf = (PredicateFormula)f;
                                    CompoundFormula cfOr = new CompoundFormula("or");
                                    cfOr.AddOperand(pf);
                                    foreach (PredicateFormula pfOrg in lPredicateOperands)
                                        cfOr.AddOperand(pfOrg);
                                    lClauses.Add(cfOr);
                                }
                                else
                                {
                                    CompoundFormula cf = (CompoundFormula)f;
                                    if (cf.Operator == "or")
                                    {
                                        CompoundFormula cfOr = new CompoundFormula("or");
                                        foreach (PredicateFormula pf in cf.Operands)
                                        {
                                            cfOr.AddOperand(pf);
                                        }
                                        foreach (PredicateFormula pfOrg in lPredicateOperands)
                                            cfOr.AddOperand(pfOrg);
                                        lClauses.Add(cfOr);
                                    }

                                }
                            }
                        }
                        else
                            throw new NotImplementedException();
                    }
                    else if (Operator == "oneof")
                    {
                        CompoundFormula cfOr = new CompoundFormula("or");
                        List<Predicate> lPredicates = new List<Predicate>();
                        foreach (PredicateFormula pf in Operands)
                        {
                            lPredicates.Add(pf.Predicate);
                            cfOr.AddOperand(pf);
                        }
                        lClauses.Add(cfOr);
                        for (int i = 0; i < lPredicates.Count - 1; i++)
                        {
                            for (int j = i + 1; j < lPredicates.Count; j++)
                            {
                                cfOr = new CompoundFormula("or");
                                cfOr.AddOperand(lPredicates[i].Negate());
                                cfOr.AddOperand(lPredicates[j].Negate());
                                lClauses.Add(cfOr);
                            }
                        }
                    }
                    else if (Operator == "and")
                    {
                        foreach (Formula f in Operands)
                        {
                            if (f is CompoundFormula)
                                lClauses.Add((CompoundFormula)f);
                            else
                            {
                                CompoundFormula cfOr = new CompoundFormula("or");
                                cfOr.AddOperand(f);
                                lClauses.Add(cfOr);
                            }
                        }
                    }
                    else
                        throw new NotImplementedException();

                    return lClauses;
                }
        */

        private CompoundFormula RemoveOneof(out bool bChanged)
        {
            if (Operator == "oneof")
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                CompoundFormula cfOr = new CompoundFormula("or");
                List<Formula> lOperands = new List<Formula>();
                foreach (Formula f in Operands)
                {
                    lOperands.Add(f);
                    cfOr.AddOperand(f);
                }
                cfAnd.AddOperand(cfOr);
                for (int i = 0; i < lOperands.Count - 1; i++)
                {
                    for (int j = i + 1; j < lOperands.Count; j++)
                    {
                        cfOr = new CompoundFormula("or");
                        cfOr.AddOperand(lOperands[i].Negate());
                        cfOr.AddOperand(lOperands[j].Negate());
                        cfAnd.AddOperand(cfOr);
                    }
                }
                bChanged = true;
                return cfAnd;
            }
            bChanged = false;
            return this;
        }

        public CompoundFormula RemoveNestedConjunction(out bool bChanged)
        {
            bChanged = false;
            CompoundFormula cfAnd = new CompoundFormula("and");
            if (Operator == "or")
            {
                List<CompoundFormula> lCompoundOperands = new List<CompoundFormula>();
                List<PredicateFormula> lPredicateOperands = new List<PredicateFormula>();
                foreach (Formula f in Operands)
                {
                    if (f is CompoundFormula)
                    {
                        CompoundFormula cf = (CompoundFormula)f;
                        cf = cf.RemoveNestedConjunction(out bChanged);
                        lCompoundOperands.Add(cf);
                    }
                    else
                        lPredicateOperands.Add((PredicateFormula)f);
                }
                if (lCompoundOperands.Count == 0)
                {
                    return this;
                }
                List<List<Formula>> lAllCombinations = GetAllCombinations(lPredicateOperands, lCompoundOperands);
                foreach (List<Formula> lCombination in lAllCombinations)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (Formula f in lCombination)
                        cfOr.AddOperand(f);
                    foreach (PredicateFormula f in lPredicateOperands)
                        cfOr.AddOperand(f);
                    if (!cfOr.IsTrue(new List<Predicate>()))
                        cfAnd.AddOperand(cfOr);
                }
                /*
            else if (lCompoundOperands.Count == 1)
            {
                CompoundFormula cfNestedAnd = lCompoundOperands[0];
                if (cfNestedAnd.Operator != "and")
                    throw new NotImplementedException();
                foreach (Formula f in cfNestedAnd.Operands)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    cfOr.AddOperand(f);
                    foreach (PredicateFormula pfOrg in lPredicateOperands)
                        cfOr.AddOperand(pfOrg);
                    cfAnd.AddOperand(cfOr);
                }
            }
            else
                throw new NotImplementedException();
                 * */
                bChanged = true;
            }
            else
            {
                foreach (Formula f in Operands)
                {
                    if (f is CompoundFormula)
                    {
                        CompoundFormula cf = (CompoundFormula)f;
                        cf = cf.RemoveNestedConjunction(out bChanged);
                        if (cf.Operands.Count > 0)
                        {
                            if (cf.Operator == "and")
                                foreach (Formula fSub in cf.Operands)
                                    cfAnd.AddOperand(fSub);
                            else
                                cfAnd.AddOperand(cf);
                        }
                    }
                    else
                        cfAnd.AddOperand(f);
                }
            }
            return cfAnd;
        }

        private List<List<Formula>> GetAllCombinations(List<PredicateFormula> lPredicateOperands, List<CompoundFormula> lCompoundOperands)
        {
            return GetAllCombinations(lPredicateOperands, lCompoundOperands, 0);
        }

        private List<List<Formula>> GetAllCombinations(List<PredicateFormula> lPredicateOperands, List<CompoundFormula> lCompoundOperands, int idx)
        {
            List<List<Formula>> lCurrent = new List<List<Formula>>();
            if (lCompoundOperands[idx].Operator != "and")
                throw new NotImplementedException();
            List<List<Formula>> lRec = null;
            if (idx < lCompoundOperands.Count - 1)
                lRec = GetAllCombinations(lPredicateOperands, lCompoundOperands, idx + 1);
            foreach (Formula f in lCompoundOperands[idx].Operands)
            {
                if (!lPredicateOperands.Contains(f.Negate()))
                {
                    if (idx == lCompoundOperands.Count - 1)
                    {
                        List<Formula> lNew = new List<Formula>();
                        lNew.Add(f);
                        lCurrent.Add(lNew);
                    }
                    else
                    {
                        foreach (List<Formula> l in lRec)
                        {
                            if (!l.Contains(f.Negate()))
                            {
                                List<Formula> lNew = new List<Formula>();
                                lNew.AddRange(l);
                                lNew.Add(f);
                                lCurrent.Add(lNew);
                            }
                        }
                    }
                }
            }
            return lCurrent;
        }

        public bool IsSimpleOneOf()
        {
            if (Operator != "oneof")
                return false;
            foreach (Formula f in Operands)
            {
                if (f is CompoundFormula)
                    return false;
            }
            return true;
        }

        public override Formula ToCNF()
        {
            if (Operator == "and")
            {
                if (IsSimpleFormula())
                    return this;
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (Formula fSub in Operands)
                    cfAnd.AddOperand(fSub.ToCNF());
                return cfAnd;

            }
            else if (Operator == "or")
            {
                if (IsSimpleFormula())
                    return this;
                List<Formula> lConverted = new List<Formula>();
                foreach (Formula fSub in Operands)
                    lConverted.Add(fSub.ToCNF());
                List<Formula> lAllCombinations = GetAllCombinations(lConverted, 0);
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (Formula f in lAllCombinations)
                    cfAnd.AddOperand(f);
                return cfAnd;
            }
            else
                throw new NotImplementedException();
            return null;
        }

        private List<Formula> GetAllCombinations(List<Formula> lConverted, int idx)
        {
            List<Formula> lCombinations = new List<Formula>();
            if (idx == lConverted.Count - 1)
            {
                if (lConverted[idx] is CompoundFormula)
                {
                    CompoundFormula cf = (CompoundFormula)lConverted[idx];
                    foreach (Formula fSub in cf.Operands)
                        lCombinations.Add(fSub);
                }
                else
                    lCombinations.Add(lConverted[idx]);
            }
            else
            {

                List<Formula> lRec = GetAllCombinations(lConverted, idx + 1);
                if (lConverted[idx] is CompoundFormula)
                {
                    CompoundFormula cf1 = (CompoundFormula)lConverted[idx];
                    foreach (Formula fSub1 in cf1.Operands)
                    {
                        foreach (Formula f2 in lRec)
                        {
                            CompoundFormula cfOr = new CompoundFormula("or");
                            cfOr.AddOperand(fSub1);
                            cfOr.AddOperand(f2);
                            if (!cfOr.IsTrue(null))
                                lCombinations.Add(cfOr);
                        }
                    }

                }
                else
                {
                    foreach (Formula f2 in lRec)
                    {
                        CompoundFormula cfOr = new CompoundFormula("or");
                        cfOr.AddOperand(lConverted[idx]);
                        cfOr.AddOperand(f2);
                        if (!cfOr.IsTrue(null))
                            lCombinations.Add(cfOr);
                    }

                }
            }

            return lCombinations;
        }

        public CompoundFormula ToCNF2()
        {
            if (IsSimpleFormula())
                return this;
            if (IsCNF())
                return this;
            if (IsSimpleDisjunction())
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(this);
                return cfAnd;
            }
            bool bChanged = true;
            CompoundFormula cfRevised = new CompoundFormula(Operator);
            List<CompoundFormula> lSimpleOneOf = new List<CompoundFormula>();
            foreach (Formula f in Operands)
            {
                if (f is CompoundFormula)
                {
                    CompoundFormula cf = (CompoundFormula)f;
                    if (cf.IsSimpleOneOf())
                        lSimpleOneOf.Add(cf);
                    else
                        cfRevised.AddOperand(((CompoundFormula)f).RemoveOneof(out bChanged));
                }
                else
                    cfRevised.AddOperand(f);
            }
            cfRevised = (CompoundFormula)cfRevised.Simplify();
            bChanged = true;
            while (bChanged)
            {
                bChanged = false;
                cfRevised = (CompoundFormula)cfRevised.RemoveNestedConjunction(out bChanged);
            }
            /*
            if (cfRevised.Operator != "and")
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(cfRevised);
                cfRevised = cfAnd;
            }
             */
            foreach (CompoundFormula cf in lSimpleOneOf)
                cfRevised.AddOperand(cf);
            Debug.Assert(cfRevised.IsCNF());
            return cfRevised;
        }

        public override bool ContainsNonDeterministicEffect()
        {
            if (Operator == "or" || Operator == "oneof")
                return true;
            if (Operator == "and")
            {
                foreach (Formula f in Operands)
                    if (f.ContainsNonDeterministicEffect())
                        return true;
                return false;
            }
            if (Operator == "when")
                return Operands[1].ContainsNonDeterministicEffect();
            throw new NotImplementedException();
        }

        public override int GetMaxNonDeterministicOptions()
        {
            if (Operator == "or" || Operator == "oneof")
                return Operands.Count;
            if (Operator == "and")
            {
                int iMax = 0, iCurrent = 0;
                foreach (Formula f in Operands)
                {
                    iCurrent = f.GetMaxNonDeterministicOptions();
                    if (iCurrent > iMax)
                        iMax = iCurrent;
                }
                return iMax;
            }
            if (Operator == "when")
                return Operands[1].GetMaxNonDeterministicOptions();
            throw new NotImplementedException();
        }
        public override void GetNonDeterministicOptions(List<CompoundFormula> lOptions)
        {
            if (Operator == "or" || Operator == "oneof")
                lOptions.Add(this);
            else if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    f.GetNonDeterministicOptions(lOptions);
                }
            }
            else if (Operator == "when")
            {
                if (Operands[1].ContainsNonDeterministicEffect())
                    lOptions.Add(this);
            }
            else
                throw new NotImplementedException();
        }

        public Formula ChooseOption(int iOption)
        {
            if (Operator == "or" || Operator == "oneof")
            {
                //in or there could be more than a single option - not implemented here
                int iActualOption = iOption % Operands.Count;
                return Operands[iActualOption].Clone();
            }
            if (Operator == "and")
            {
                CompoundFormula cfNew = new CompoundFormula("and");
                foreach (Formula fOperand in Operands)
                {
                    if (fOperand is CompoundFormula)
                    {
                        cfNew.AddOperand(((CompoundFormula)fOperand).ChooseOption(iOption));
                    }
                    else
                        cfNew.AddOperand(fOperand);
                }
                return cfNew;
            }
            if (Operator == "when")
            {
                CompoundFormula cfNew = new CompoundFormula("when");
                CompoundFormula cfGiven = new CompoundFormula("and");
                cfGiven.AddOperand(Operands[0].Clone());
                cfNew.AddOperand(cfGiven);
                cfNew.AddOperand(((CompoundFormula)Operands[1]).ChooseOption(iOption));
                return cfNew;
            }
            throw new NotFiniteNumberException();
        }



        public override void GetAllOptionalPredicates(HashSet<Predicate> lPredicates)
        {
            if (Operator == "or" || Operator == "oneof")
            {
                foreach (Formula f in Operands)
                {
                    //from now on everything is optional so we jsut add them
                    f.GetAllPredicates(lPredicates);
                }
            }
            else if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    f.GetAllOptionalPredicates(lPredicates);
                }
            }
            else if (Operator == "when")
                Operands[1].GetAllOptionalPredicates(lPredicates);
            else
                throw new NotImplementedException();
        }

        public int GetChoiceIndex(Predicate p)
        {
            if (Operator == "or" || Operator == "oneof")
            {
                for (int i = 0; i < Operands.Count; i++)
                {
                    HashSet<Predicate> lPredicates = Operands[i].GetAllPredicates();
                    if (lPredicates.Contains(p))
                        return i;
                }
            }
            else if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    if (f is CompoundFormula)
                    {
                        int iChoice = ((CompoundFormula)f).GetChoiceIndex(p);
                        if (iChoice != -1)
                            return iChoice;
                    }
                }
            }
            else if (Operator == "when" && Operands[1] is CompoundFormula)
                return ((CompoundFormula)Operands[1]).GetChoiceIndex(p);

            return -1;
        }

        public int GetOtherChoiceIndex(Predicate p)
        {
            if (Operator == "or" || Operator == "oneof")
            {
                for (int i = 0; i < Operands.Count; i++)
                {
                    HashSet<Predicate> lPredicates = Operands[i].GetAllPredicates();
                    if (!lPredicates.Contains(p))
                        return i;
                }
            }
            else if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    if (f is CompoundFormula)
                    {
                        int iChoice = ((CompoundFormula)f).GetOtherChoiceIndex(p);
                        if (iChoice != -1)
                            return iChoice;
                    }
                }
            }
            else if (Operator == "when" && Operands[1] is CompoundFormula)
                return ((CompoundFormula)Operands[1]).GetOtherChoiceIndex(p);

            return -1;
        }

        public override Formula CreateRegression(Predicate p, int iChoice)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                cfNew.AddOperand(f.CreateRegression(p, iChoice));
            return cfNew;
        }

        public override Formula GenerateGiven(string sTag, List<string> lAlwaysKnown)
        {
            CompoundFormula cfGiven = new CompoundFormula(Operator);
            foreach (Formula fOperand in Operands)
                cfGiven.AddOperand(fOperand.GenerateGiven(sTag, lAlwaysKnown));
            return cfGiven;
        }

        public override Formula AddTime(int iTime)
        {
            CompoundFormula cf = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                cf.AddOperand(f.AddTime(iTime));
            return cf;
        }



        public CompoundFormula ToDNF()
        {
            CompoundFormula cfDNF = new CompoundFormula("or");
            if (Operator == "or")
            {
                foreach (Formula fSub in Operands)
                {
                    if (fSub is PredicateFormula)
                        cfDNF.AddOperand(fSub);
                    else
                    {
                        CompoundFormula cfSub = (CompoundFormula)fSub;
                        if (cfSub.IsSimpleConjunction())
                            cfDNF.AddOperand(fSub);
                        else
                            throw new NotImplementedException();
                    }
                }

            }
            if (Operator == "and")
            {
                List<CompoundFormula> lSubExpressions = new List<CompoundFormula>();
                lSubExpressions.Add(new CompoundFormula("and"));
                foreach (Formula fSub in Operands)
                {
                    if (fSub is PredicateFormula)
                    {
                        foreach (CompoundFormula cf in lSubExpressions)
                            cf.AddOperand(fSub);
                    }
                    else
                    {
                        CompoundFormula cfSub = (CompoundFormula)fSub;
                        if (cfSub.IsSimpleConjunction())
                        {
                            foreach (CompoundFormula cf in lSubExpressions)
                                cf.AddOperand(fSub);
                        }
                        else if (cfSub.IsSimpleDisjunction())
                        {
                            int cOperands = cfSub.Operands.Count;
                            int cCurrentExpressions = lSubExpressions.Count;
                            for (int iOperand = 1; iOperand < cOperands; iOperand++)
                            {
                                for (int iSubExpression = 0; iSubExpression < cCurrentExpressions; iSubExpression++)
                                {
                                    CompoundFormula cfNew = (CompoundFormula)lSubExpressions[iSubExpression].Clone();
                                    cfNew.AddOperand(cfSub.Operands[iOperand]);
                                    lSubExpressions.Add(cfNew);
                                }
                            }
                            for (int iSubExpression = 0; iSubExpression < cCurrentExpressions; iSubExpression++)
                            {
                                lSubExpressions[iSubExpression].AddOperand(cfSub.Operands[0]);
                            }
                        }
                        else
                            throw new NotImplementedException();
                    }
                }
                foreach (CompoundFormula cf in lSubExpressions)
                    cfDNF.AddOperand(cf);
            }
            return cfDNF;
        }


        public override Formula ReplaceNegativeEffectsInCondition()
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            if (Operator == "when")
            {
                cfNew.AddOperand(Operands[0]);
                cfNew.AddOperand(Operands[1].ReplaceNegativeEffectsInCondition());
            }
            else
            {
                foreach (Formula f in Operands)
                    cfNew.AddOperand(f.ReplaceNegativeEffectsInCondition());
            }
            return cfNew;
        }

        public string ToInvariant()
        {
            string sOutput = "";
            /*
            if (Operator == "oneof")
            {
                if(Operands.Count > 2)
                    throw new NotImplementedException("handling only 2 operands in oneof");
                sOutput += "(invariant " + Operands[0] + " " + Operands[1] + ")";
                sOutput += " (invariant " + Operands[0].Negate() + " " + Operands[1].Negate() + ")";
            }
            else if (Operator == "or")
            {
                sOutput = "(invariant";
                foreach (Formula f in Operands)
                {
                    sOutput += " " + f;
                }
                sOutput += ")";
            }
             */
            if (Operator == "or" || Operator == "oneof")
            {
                sOutput = "(invariant";
                foreach (Formula f in Operands)
                {
                    sOutput += " " + f;
                }
                sOutput += ")";
            }
            else
                throw new NotImplementedException("handling only oneof, or");
            return sOutput;
        }

        public override Formula RemoveImpossibleOptions(IEnumerable<Predicate> lObserved)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    Formula fTag = f;
                    if (f is CompoundFormula)
                    {
                        fTag = ((CompoundFormula)f).RemoveImpossibleOptions(lObserved);
                    }
                    if (fTag == null)
                        return null;
                    cfNew.AddOperand(fTag);
                }
            }
            else if (Operator == "or")
            {
                foreach (Formula f in Operands)
                {
                    Formula fTag = f;
                    if (f is CompoundFormula)
                    {
                        fTag = ((CompoundFormula)f).RemoveImpossibleOptions(lObserved);
                    }
                    if (fTag != null)
                        cfNew.AddOperand(fTag);
                }
            }
            else if (Operator == "when")
            {
                Formula fTag = ((CompoundFormula)Operands[1]).RemoveImpossibleOptions(lObserved);
                if (fTag != null)
                {
                    cfNew.AddOperand(Operands[0]);
                    cfNew.AddOperand(fTag);
                }
                else
                    return null;
            }
            else
                throw new NotImplementedException();
            return cfNew;
        }

        public override Formula ApplyKnown(IEnumerable<Predicate> lKnown)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            if (Operator == "and" || Operator == "or" || Operator == "oneof")
            {
                foreach (Formula f in Operands)
                {
                    Formula fTag = f.ApplyKnown(lKnown);
                    if (fTag != null)
                        cfNew.SimpleAddOperand(fTag);
                }
            }
            else if (Operator == "when")
            {
                if (Operands[0].IsTrue(lKnown))
                    return Operands[1];
                if (Operands[0].IsFalse(lKnown))
                    return null;
                cfNew.AddOperand(Operands[0].ApplyKnown(lKnown));
                cfNew.AddOperand(Operands[1]);
            }
            else
                throw new NotImplementedException();
            return cfNew;
        }

        public override Formula ReduceConditions(IEnumerable<Predicate> lKnown)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            if (Operator == "and")// || Operator == "or" || Operator == "oneof")
            {
                foreach (Formula f in Operands)
                {
                    if (f is CompoundFormula)
                    {
                        Formula fTag = f.ReduceConditions(lKnown);
                        if (fTag != null)
                            cfNew.SimpleAddOperand(fTag);
                    }
                    else
                        cfNew.SimpleAddOperand(f);
                }
            }
            else if (Operator == "when")
            {
                Formula fReduced = Operands[0].Reduce(lKnown);
                if (fReduced.IsTrue(null))
                    return Operands[1];
                if (fReduced.IsFalse(null))
                    return null;
                cfNew.AddOperand(fReduced);
                cfNew.AddOperand(Operands[1]);
            }
            else if ((Operator == "or" || Operator == "oneof") && IsSimpleFormula())
                return this;
            else
                throw new NotImplementedException();
            return cfNew;
        }

        public CompoundFormula RemoveNonDeterminism(int iActionIndex, ref int iChoiceIndex, CompoundFormula cfAndChoices)
        {
            CompoundFormula cfNew = null;
            if (Operator == "and")
            {
                cfNew = new CompoundFormula("and");
                foreach (Formula f in Operands)
                {
                    if (f is PredicateFormula)
                    {
                        cfNew.AddOperand(f);
                    }
                    else
                    {
                        CompoundFormula cfOperand = ((CompoundFormula)f).RemoveNonDeterminism(iActionIndex, ref iChoiceIndex, cfAndChoices);
                        cfNew.AddOperand(cfOperand);
                    }
                }
            }
            else if (Operator == "oneof" || Operator == "or")
            {
                cfNew = new CompoundFormula("and");
                CompoundFormula cfChoices = new CompoundFormula(Operator);
                foreach (Formula f in Operands)
                {
                    GroundedPredicate pChoice = new GroundedPredicate("Choice");
                    pChoice.AddConstant(new Constant("ActionIndex", "a" + iActionIndex));
                    pChoice.AddConstant(new Constant("ChoiceIndex", "c" + iChoiceIndex));
                    iChoiceIndex++;

                    CompoundFormula cfWhen = new CompoundFormula("when");
                    cfWhen.AddOperand(pChoice);
                    cfWhen.AddOperand(f);
                    cfNew.AddOperand(cfWhen);

                    cfChoices.AddOperand(pChoice);
                }
                cfAndChoices.AddOperand(cfChoices);
            }
            else if (Operator == "when")
            {
                if (Operands[1] is PredicateFormula)
                    return this;
                CompoundFormula cfSecond = ((CompoundFormula)Operands[1]).RemoveNonDeterminism(iActionIndex, ref iChoiceIndex, cfAndChoices);
                bool bInserted = false;
                cfNew = cfSecond.InsertGiven(Operands[0], out bInserted);
                if (!bInserted)
                {
                    cfNew = new CompoundFormula("when");
                    cfNew.AddOperand(Operands[0]);
                    cfNew.AddOperand(cfSecond);
                }
                /*
                cfNew = new CompoundFormula("when");
                if (cfSecond.Operator == "and")
                {
                    cfNew.AddOperand(Operands[0]);
                    cfNew.AddOperand(cfSecond);
                }
                else if (cfSecond.Operator == "when")
                {
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    cfAnd.AddOperand(Operands[0]);
                    cfAnd.AddOperand(cfSecond.Operands[0]);
                    cfNew.AddOperand(cfAnd);
                    cfNew.AddOperand(cfSecond.Operands[1]);


                }
                 * */
            }
            else if (Operator == "not")
            {
                cfNew = new CompoundFormula("not");
                if (cfNew.Operands[0] is PredicateFormula)
                    cfNew.AddOperand(Operands[0]);
                else
                    cfNew.AddOperand(((CompoundFormula)Operands[0]).RemoveNonDeterminism(iActionIndex, ref iChoiceIndex, cfAndChoices));
            }
            else
                throw new NotImplementedException();
            return cfNew;
        }

        private CompoundFormula InsertGiven(Formula fGiven, out bool bInserted)
        {
            CompoundFormula cfNew = new CompoundFormula(Operator);
            bInserted = false;
            if (Operator == "when")
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(Operands[0]);
                cfAnd.AddOperand(fGiven);
                cfNew.AddOperand(cfAnd);
                cfNew.AddOperand(Operands[1]);
                bInserted = true;
            }
            else if (Operator == "and")
            {
                foreach (Formula f in Operands)
                {
                    if (f is PredicateFormula)
                        cfNew.AddOperand(f);
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)f;
                        cfNew.AddOperand(cf.InsertGiven(fGiven, out bInserted));
                    }

                }

            }
            else if (Operator == "not")
            {
                return this;//when cannot be inside a negation (I think)
            }
            else
                throw new NotImplementedException();
            return cfNew;
        }

        public override List<Predicate> GetNonDeterministicEffects()
        {
            List<Predicate> lNonDetPredicates = new List<Predicate>();
            if (Operator == "when")
            {
                return Operands[1].GetNonDeterministicEffects();
            }
            else if (Operator == "and" || Operator == "not")
            {
                foreach (Formula f in Operands)
                {
                    lNonDetPredicates.AddRange(f.GetNonDeterministicEffects());
                }
            }
            else if (Operator == "or" || Operator == "oneof")
            {
                return new List<Predicate>(GetAllPredicates());
            }
            else
                throw new NotImplementedException();
            return lNonDetPredicates;
        }

        public override Formula RemoveUniversalQuantifiers(List<Constant> lConstants, List<Predicate> lConstantPredicates, Domain d)
        {
            CompoundFormula fNew = new CompoundFormula(Operator);
            //if (ToString().Contains("faulty") && !ToString().Contains("P_FALSE"))
            //    Debug.WriteLine("**");
            foreach (Formula f in Operands)
            {
                Formula fRemoved = f.RemoveUniversalQuantifiers(lConstants, lConstantPredicates, d);
                if (fRemoved != null)
                {
                    if (fRemoved is PredicateFormula)
                    {
                        Predicate p = ((PredicateFormula)fRemoved).Predicate;
                        if (p == Domain.TRUE_PREDICATE)
                        {
                            if (Operator == "and")
                                continue;
                            if (Operator == "or")
                                return fRemoved;
                            if (Operator == "when")
                            {
                                if (fNew.Operands.Count == 0)
                                {
                                    fNew.Operator = "and";
                                    continue;
                                }
                                else
                                    throw new NotImplementedException();
                            }
                            else
                                throw new NotImplementedException();
                        }
                        if (p == Domain.FALSE_PREDICATE)
                        {
                            if (Operator == "and")
                                return fRemoved;
                            if (Operator == "or")
                                continue;
                            if (Operator == "when")
                            {
                                if (fNew.Operands.Count == 0)
                                {
                                    return null;
                                }
                                else
                                    throw new NotImplementedException();
                            }
                            else
                                throw new NotImplementedException();
                        }
                    }


                    fNew.AddOperand(fRemoved);
                }
            }

            if (fNew.Operands.Count == 0)
            {
                if (Operator == "and")
                    return new PredicateFormula(Domain.TRUE_PREDICATE);
                if (Operator == "or" || Operator == "oneof")
                    return new PredicateFormula(Domain.FALSE_PREDICATE);
            }

            Formula fSimplified = fNew.Simplify();

            return fSimplified;
        }

        public override Formula GetKnowledgeFormula(List<string> lAlwaysKnown, bool bKnowWhether)
        {
            CompoundFormula cfK = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
                cfK.AddOperand(f.GetKnowledgeFormula(lAlwaysKnown, bKnowWhether));
            return cfK;
        }

        public void SplitAddRemove(Dictionary<Predicate, Predicate> dTaggedPredicates, out CompoundFormula cfAddCondition, out CompoundFormula cfRemoveCondition)
        {
            if (Operator != "when")
                throw new NotImplementedException();
            cfAddCondition = null;
            cfRemoveCondition = null;
            if (Operands[1] is PredicateFormula)
            {
                PredicateFormula fEffect = (PredicateFormula)Operands[1];
                if (fEffect.Predicate.Negation)
                    cfRemoveCondition = this;
                else
                    cfAddCondition = this;
                return;
            }
            CompoundFormula cfEffect = (CompoundFormula)Operands[1];
            CompoundFormula cfAddEffects = new CompoundFormula("and"), cfRemoveEffects = new CompoundFormula("and");
            if (cfEffect.Operator == "and")
            {
                foreach (PredicateFormula fOperand in cfEffect.Operands)
                {
                    Predicate pTag = fOperand.Predicate.ToTag();
                    dTaggedPredicates[pTag] = fOperand.Predicate;

                    if (fOperand.Predicate.Negation)
                        cfAddEffects.AddOperand(pTag);
                    else
                        cfRemoveEffects.AddOperand(pTag);
                }
                if (cfRemoveEffects.Operands.Count > 0)
                {
                    cfRemoveCondition = new CompoundFormula("when");
                    cfRemoveCondition.AddOperand(Operands[0]);
                    cfRemoveCondition.AddOperand(cfRemoveEffects);
                }
                if (cfAddEffects.Operands.Count > 0)
                {
                    cfAddCondition = new CompoundFormula("when");
                    cfAddCondition.AddOperand(Operands[0]);
                    cfAddCondition.AddOperand(cfAddEffects);
                }

            }
            else
                throw new NotImplementedException();
        }

        public void IdentifyDisjunctions(List<List<Formula>> lOptions, HashSet<Predicate> hsMandatory)
        {
            if (Operator == "or" || Operator == "oneof")
            {
                List<Formula> lNewOption = new List<Formula>();
                foreach (Formula fSub in Operands)
                    lNewOption.Add(fSub);
                lOptions.Add(lNewOption);
            }
            else if (Operator == "and")
            {
                foreach (Formula fSub in Operands)
                {
                    if (fSub is CompoundFormula)
                        ((CompoundFormula)fSub).IdentifyDisjunctions(lOptions, hsMandatory);
                    else
                        hsMandatory.Add(((PredicateFormula)fSub).Predicate);
                }

            }
            else
                throw new NotImplementedException();
        }

        public override Formula RemoveNegations()
        {
            CompoundFormula cf = new CompoundFormula(Operator);
            foreach (Formula f in Operands)
            {
                Formula fRemoved = f.RemoveNegations();
                if (f != null)
                {
                    cf.AddOperand(fRemoved);
                }
            }
            return cf;
        }


        public List<Formula> GetAllOptions()
        {
            List<Formula> l = new List<Formula>();

            if (IsSimpleOneOf())
            {
                foreach (Formula f in Operands)
                    l.Add(f);
                return l;
            }
            if (IsSimpleDisjunction())
            {
                return GetAllOptions(Operands, 0);
            }
            throw new NotImplementedException();
        }
        private List<Formula> GetAllOptions(List<Formula> lSubFormulas, int idx)
        {
            List<Formula> l = new List<Formula>();
            l.Add(lSubFormulas[idx]);
            if (idx == l.Count - 1)
            {
                return l;
            }
            List<Formula> lRest = GetAllOptions(lSubFormulas, idx + 1);
            foreach (Formula f in lRest)
            {
                l.Add(f);
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(f);
                cfAnd.AddOperand(lSubFormulas[idx]);
                l.Add(cfAnd);
            }
            return l;
        }

    }
}
