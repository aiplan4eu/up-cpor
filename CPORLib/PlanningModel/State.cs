using CPORLib.LogicalUtilities;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Action = CPORLib.PlanningModel.PlanningAction;

namespace CPORLib.PlanningModel
{
    public class State
    {
        public ISet<Predicate> Predicates { get { return new UnifiedSet<Predicate>(m_lAlwaysTrue,m_lChangingPredicates); } }
        
        //protected HashSet<Predicate> m_lPredicates;

        protected HashSet<Predicate> m_lAlwaysTrue;
        protected HashSet<Predicate> m_lChangingPredicates;

        public List<Action> AvailableActions { get; protected set; }
        public State Predecessor { private set; get; }
        public PlanningAction GeneratingAction { private set; get; }
        public List<string> History { private set; get; }
        public bool MaintainNegations { get; private set; }
        public Problem Problem { get; private set; }
        public int ID { get; private set; }
        public Dictionary<string, double> FunctionValues { get; private set; }
        public int Time { get; private set; }
        public int ChoiceCount { get; private set; }

        public static int STATE_COUNT = 0;

        public State(Problem p)
        {
            Problem = p;
            Predecessor = null;
            //m_lPredicates = new HashSet<Predicate>();
            m_lAlwaysTrue = new HashSet<Predicate>();
            m_lChangingPredicates = new HashSet<Predicate>();
            AvailableActions = new List<Action>();
            MaintainNegations = true;
            ID = STATE_COUNT++;
            FunctionValues = new Dictionary<string, double>();
            Time = 0;
            ChoiceCount = 0;
            foreach (string sFunction in Problem.Domain.Functions)
            {
                FunctionValues[sFunction] = 0.0;
            }
            History = new List<string>();
            History.Add(ToString());
        }
        public State(State sPredecessor)
            : this(sPredecessor.Problem)
        {
            Predecessor = sPredecessor;
            //m_lPredicates = new HashSet<Predicate>(sPredecessor.m_lPredicates);
            m_lChangingPredicates = new HashSet<Predicate>(Predecessor.m_lChangingPredicates);

            
            m_lAlwaysTrue = Predecessor.m_lAlwaysTrue;

            

            FunctionValues = new Dictionary<string, double>();
            foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                FunctionValues[p.Key] = p.Value;
            Time = sPredecessor.Time + 1;
            MaintainNegations = sPredecessor.MaintainNegations;
        }

        public bool ConsistentWith(Predicate p)
        {
            foreach (Predicate pState in Predicates)
            {
                if (!p.ConsistentWith(pState))
                    return false;
            }
            return true;
        }

        public bool ConsistentWith(Formula f)
        {
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f;
                bool bConsistent = false;
                foreach (Formula fOperand in cf.Operands)
                {
                    bConsistent = ConsistentWith(fOperand);
                    if (cf.Operator == "and" && !bConsistent)
                        return false;
                    if (cf.Operator == "or" && bConsistent)
                        return true;
                    if (cf.Operator == "not")
                        return !bConsistent;
                }
                if (cf.Operator == "and")
                    return true;
                if (cf.Operator == "or")
                    return false;
            }
            else
            {
                PredicateFormula vf = (PredicateFormula)f;
                return ConsistentWith(vf.Predicate);
            }
            return false;
        }


        public void RemovePredicate(Predicate p)
        {
            //m_lPredicates.Remove(p);
            m_lChangingPredicates.Remove(p);
        }

        public void AddPredicate(Predicate p)
        {
            if (!MaintainNegations && p.Negation)
                return;
            //m_lPredicates.Add(p);
            if (Problem.Domain.AlwaysConstant(p))
            {
                m_lAlwaysTrue.Add(p);
            }
            else
                m_lChangingPredicates.Add(p);
            
        }

        public override bool Equals(object obj)
        {
            if (obj is State)
            {
                State s = (State)obj;
                if (s.m_lChangingPredicates.Count != m_lChangingPredicates.Count)
                    return false;

                if (s.GetHashCode() != GetHashCode())
                    return false;

                foreach (Predicate p in s.m_lChangingPredicates)
                    if (!m_lChangingPredicates.Contains(p))
                        return false;
                return true;

                //return m_lPredicates.Equals(s.m_lPredicates);
            }
            return false;
        }
        public virtual void GroundAllActions()
        {
            ISet<Predicate> all = new UnifiedSet<Predicate>(m_lAlwaysTrue, m_lChangingPredicates);
            AvailableActions = Problem.Domain.GroundAllActions(all, MaintainNegations);
        }
        public bool Contains(Formula f)
        {
            ISet<Predicate> all = new UnifiedSet<Predicate>(m_lAlwaysTrue, m_lChangingPredicates);
            return f.ContainedIn(all, false);
        }
        public virtual State Clone()
        {
            //BUGBUG; //very slow? remove negations?
            return new State(this);
        }
        /*
        public State Apply(string sActionName)
        {
            sActionName = sActionName.Replace(' ', '_');//moving from ff format to local format
            if (AvailableActions.Count == 0)
                GroundAllActions(Problem.Domain.Actions);
            foreach (Action a in AvailableActions)
                if (a.Name == sActionName)
                    return Apply(a);
            return null;
        }
         * */
        public State Apply(string sActionName)
        {
            string sRevisedActionName = sActionName.Replace(Utilities.DELIMITER_CHAR, " ");
            string[] aName = Utilities.SplitString(sRevisedActionName, ' ');
            Action a = Problem.Domain.GroundActionByName(aName);
            if (a == null)
                return null;
            return Apply(a);
        }



        public State Apply(Action a)
        {
            //Debug.WriteLine("Executing " + a.Name);
            if (a is ParametrizedAction)
                return null;
            ISet<Predicate> all = new UnifiedSet<Predicate>(m_lAlwaysTrue, m_lChangingPredicates);

            //if (m_lPredicates.Count != all.Count)
            //    Console.Write("*");

            if (a.Preconditions != null && !a.Preconditions.IsTrue(all, MaintainNegations))
                return null;

            State sNew = Clone();

            sNew.GeneratingAction = a;
            sNew.History = new List<string>(History);
            sNew.History.Add(ToString());
            sNew.History.Add(a.Name);

            sNew.Time = Time + 1;

            if (a.Effects == null)
                return sNew;

            if (a.Effects != null)
            {
                /*
                if (a.HasConditionalEffects)
                {
                    sNew.AddEffects(a.GetApplicableEffects(m_lPredicates, MaintainNegations));
                }
                else
                {
                    sNew.AddEffects(a.Effects);
                }
                 * */
                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                GetApplicableEffects(a.Effects, lAddList, lDeleteList);
                foreach (Predicate p in lDeleteList)
                    sNew.AddEffect(p);
                foreach (Predicate p in lAddList)
                    sNew.AddEffect(p);
                //sNew.AddEffects(a.Effects);
            }
            if (!MaintainNegations)
                sNew.RemoveNegativePredicates();
            if (sNew.Predicates.Contains(Utilities.FALSE_PREDICATE))
                Debug.WriteLine("BUGBUG");
            return sNew;
        }
        private void AddEffect(Predicate pEffect)
        {
            if (pEffect == Utilities.FALSE_PREDICATE)
                Debug.WriteLine("BUGBUG");
            if (Problem.Domain.IsFunctionExpression(pEffect.Name))
            {
                GroundedPredicate gpIncreaseDecrease = (GroundedPredicate)pEffect;
                double dPreviousValue = Predecessor.FunctionValues[gpIncreaseDecrease.Constants[0].Name];
                double dDiff = double.Parse(gpIncreaseDecrease.Constants[1].Name);
                double dNewValue = double.NaN;
                if (gpIncreaseDecrease.Name.ToLower() == "increase")
                    dNewValue = dPreviousValue + dDiff;
                else if (gpIncreaseDecrease.Name.ToLower() == "decrease")
                    dNewValue = dPreviousValue + dDiff;
                else
                    throw new NotImplementedException();
                FunctionValues[gpIncreaseDecrease.Constants[0].Name] = dNewValue;
            }
            else //if (!m_lPredicates.Contains(pEffect))
            {
                Predicate pNegateEffect = pEffect.Negate();

                RemovePredicate(pNegateEffect);

                AddPredicate(pEffect);//we are maintaining complete state information
            }
        }
        private void AddEffects(Formula fEffects)
        {
            if (fEffects is PredicateFormula)
            {
                AddEffect(((PredicateFormula)fEffects).Predicate);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof" || cf.Operator == "or")//BUGBUG - should treat or differently
                {
                    int iRandomIdx = RandomGenerator.Next(cf.Operands.Count);
                    AddEffects(cf.Operands[iRandomIdx]);
                    GroundedPredicate pChoice = new GroundedPredicate("Choice");
                    pChoice.AddConstant(new Constant("ActionIndex", "a" + (Time - 1)));//time - 1 because this is the action that generated the state, hence its index is i-1
                    pChoice.AddConstant(new Constant("ChoiceIndex", "c" + iRandomIdx));
                    State s = this;
                    while (s != null)
                    {
                        s.AddPredicate(pChoice);
                        s = s.Predecessor;
                    }
                }
                else if (cf.Operator == "and")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        if (f is PredicateFormula)
                        {
                            AddEffect(((PredicateFormula)f).Predicate);
                        }
                        else
                            AddEffects(f);
                    }
                }
                else if (cf.Operator == "when")
                {
                    if (Predecessor.Contains(cf.Operands[0]))
                        AddEffects(cf.Operands[1]);
                }
                else
                    throw new NotImplementedException();
            }
        }

        private void GetApplicableEffects(Formula fEffects, HashSet<Predicate> lAdd, HashSet<Predicate> lDelete)
        {
            if (fEffects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)fEffects).Predicate;
                if (p.Negation)
                    lDelete.Add(p);
                else
                    lAdd.Add(p);
            }
            else if (fEffects is ProbabilisticFormula)
            {
                ProbabilisticFormula pf = (ProbabilisticFormula)fEffects;
                double dRand = RandomGenerator.NextDouble();
                double dInitialRand = dRand;
                int iOption = 0;
                while (iOption < pf.Options.Count && dRand > 0)
                {
                    dRand -= pf.Probabilities[iOption];
                    iOption++;
                }
                if (dRand < 0.01)
                {
                    iOption--;

                    GetApplicableEffects(pf.Options[iOption], lAdd, lDelete);
                }
                else //the no-op option was chosen
                {
                    iOption = -1;
                }
                GroundedPredicate pChoice = new GroundedPredicate("Choice");
                pChoice.AddConstant(new Constant("ActionIndex", "a" + Time));
                pChoice.AddConstant(new Constant("ChoiceIndex", "c" + ChoiceCount + "." + iOption));
                ChoiceCount++;
                State s = this;
                while (s != null)
                {
                    s.AddPredicate(pChoice);
                    s = s.Predecessor;
                }


            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof" || cf.Operator == "or")//BUGBUG - should treat or differently
                {
                    int iRandomIdx = RandomGenerator.Next(cf.Operands.Count);
                    GetApplicableEffects(cf.Operands[iRandomIdx], lAdd, lDelete);
                    GroundedPredicate pChoice = new GroundedPredicate("Choice");
                    pChoice.AddConstant(new Constant("ActionIndex", "a" + Time));
                    pChoice.AddConstant(new Constant("ChoiceIndex", "c" + ChoiceCount + "." + iRandomIdx));
                    ChoiceCount++;
                    State s = this;
                    while (s != null)
                    {
                        s.AddPredicate(pChoice);
                        s = s.Predecessor;
                    }
                }
                else if (cf.Operator == "and")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        GetApplicableEffects(f, lAdd, lDelete);
                    }
                }
                else if (cf.Operator == "when")
                {
                    if (Contains(cf.Operands[0]))
                        GetApplicableEffects(cf.Operands[1], lAdd, lDelete);
                }
                else if (cf is ParametrizedFormula)
                {
                    ParametrizedFormula pf = (ParametrizedFormula)cf;
                    foreach (Formula fNew in pf.Ground(Problem.Domain.Constants))
                        GetApplicableEffects(fNew, lAdd, lDelete);
                }
                else
                    throw new NotImplementedException();
            }
        }

        public Formula Observe(Formula fObserve)
        {
            if (fObserve is PredicateFormula)
            {
                Predicate pObserve = ((PredicateFormula)fObserve).Predicate;
                foreach (Predicate pCurrent in Predicates)
                {
                    if (pObserve.Equals(pCurrent))
                    {
                        return new PredicateFormula(pCurrent);
                    }
                }
                return new PredicateFormula(pObserve.Negate());
            }
            throw new NotImplementedException("Not handling compound formulas for observations");
        }

        public void RemoveNegativePredicates()
        {
            HashSet<Predicate> lFiltered = new HashSet<Predicate>();
            foreach (Predicate pObserved in m_lChangingPredicates)
            {
                if (pObserved.Negation == false)
                {
                    lFiltered.Add(pObserved);
                }
            }
            m_lChangingPredicates = lFiltered;

            lFiltered = new HashSet<Predicate>();
            foreach (Predicate pObserved in m_lAlwaysTrue)
            {
                if (pObserved.Negation == false)
                {
                    lFiltered.Add(pObserved);
                }
            }
            m_lAlwaysTrue = lFiltered;

            /*
            lFiltered = new HashSet<Predicate>();
            foreach (Predicate pObserved in m_lPredicates)
            {
                if (pObserved.Negation == false)
                {
                    lFiltered.Add(pObserved);
                }
            }
            m_lPredicates = lFiltered;
            */
            MaintainNegations = false;
        }

        private string m_sToString = null;
        public override string ToString()
        {
            if (m_sToString != null)
                return m_sToString;
            foreach (Predicate p in Predicates)
                if (p.Name == "at" && !p.Negation)
                {
                    m_sToString = p.ToString();
                    return m_sToString;
                }
            m_sToString = "";
            return m_sToString;
        }

        private int m_iHashCode = 0;
        public override int GetHashCode()
        {
            if (m_iHashCode == 0)
                m_iHashCode = ToString().GetHashCode();
            return m_iHashCode;
        }

        public bool Contains(Predicate p)
        {
            if (p.Negation)
                return !Predicates.Contains(p.Negate());
            return Predicates.Contains(p);
        }


        internal void CompleteNegations()
        {
            throw new NotImplementedException();
        }
    }
}
