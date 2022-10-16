using CPORLib.LogicalUtilities;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using static CPORLib.Tools.Options;
using Action = CPORLib.PlanningModel.PlanningAction;

namespace CPORLib.PlanningModel
{
    public class PartiallySpecifiedState
    {
        public int tmpId = 0;
        public HashSet<Action> ActionsWithConditionalEffect = null;
        public HashSet<Predicate> mayChanged = null;
        public Dictionary<GroundedPredicate, Formula> regressionFormula = null;
        public int countOfActionFromRoot = 0;
        public IEnumerable<Predicate> Observed { get { return m_lObserved; } }
        public IEnumerable<Predicate> Hidden { get { return m_lHidden; } }
        public HashSet<Predicate> m_lObserved;
        protected HashSet<Predicate> m_lHidden;
        public List<Action> AvailableActions { get; protected set; }
        private PartiallySpecifiedState m_sPredecessor;

        private List<Predicate> m_lDirectlyObserved;
        public List<Formula> deadEndList;

        public List<State> IdentifiedDeadendStates;
        public List<PartiallySpecifiedState> Parents { get; private set; }
        public Action GeneratingAction { get; private set; }
        public Formula GeneratingObservation
        {
            get
            {
                return m_fObservation;
            }
            private set
            {
                m_fObservation = value;
                if (m_fObservation != null)
                {
                    m_lHistory.Add(ID + ") " + m_fObservation.ToString());
                    if (((PredicateFormula)m_fObservation).Predicate.Negation != MishapType)
                        MishapCount++;
                    m_lDirectlyObserved.Add(((PredicateFormula)m_fObservation).Predicate);
                }

            }
        }
        public Problem Problem { get; private set; }
        public State UnderlyingEnvironmentState { get; set; }
        public BeliefState m_bsInitialBelief;

        private Formula m_fObservation;
        private List<string> m_lHistory;
        public int ChildCount { get; private set; }

        public HashSet<Predicate> m_lOfflinePredicatesKnown;
        public HashSet<Predicate> m_lOfflinePredicatesUnknown;
        public Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>> m_dRequiredObservationsForReasoning;

        public bool MishapType { get; set; }
        public int MishapCount { get; private set; }
        public int MinMishapCount { get; set; }
        public int MaxMishapCount { get; set; }

        public int Time { get; private set; }
        public CompoundFormula m_cfCNFBelief;
        private List<Predicate> m_lFailureTag;
        private List<List<Predicate>> m_lPreviousTags;

        public static int STATE_COUNT = 0;
        public int ID { get; private set; }

        public Dictionary<string, double> FunctionValues { get; private set; }
        public int oldId = 0;

        public bool ClosedState { get; private set; }
        public PartiallySpecifiedState(PartiallySpecifiedState original)
        {
            oldId = original.ID;
            ID = STATE_COUNT++;

            IdentifiedDeadendStates = new List<State>();

            m_lDirectlyObserved = new List<Predicate>(original.m_lDirectlyObserved);
            countOfActionFromRoot = original.countOfActionFromRoot;
            tmpId = original.tmpId;
            ActionsWithConditionalEffect = original.ActionsWithConditionalEffect;
            mayChanged = original.mayChanged;

            if (original.regressionFormula != null)
                regressionFormula = new Dictionary<GroundedPredicate, Formula>(original.regressionFormula);

            m_lHistory = new List<string>(original.m_lHistory);
            ChildCount = original.ChildCount;
            if (original.m_lObserved != null)
            {
                m_lObserved = new HashSet<Predicate>();
                foreach (Predicate p in original.m_lObserved)
                {
                    m_lObserved.Add(p);
                }
            }
            else
                m_lObserved = null;

            if (original.m_lHidden != null)
            {
                m_lHidden = new HashSet<Predicate>();
                foreach (Predicate p in original.m_lHidden)
                {
                    m_lHidden.Add(p);
                }
            }
            else
                m_lHidden = null;

            if (original.AvailableActions != null)
            {
                AvailableActions = new List<Action>();
                foreach (Action p in original.AvailableActions)
                {
                    AvailableActions.Add(p);
                }
            }
            else AvailableActions = null;

            m_sPredecessor = original.m_sPredecessor;
            /*PartiallySpecifiedState tempPredecessorOriginal = original.m_sPredecessor;
            PartiallySpecifiedState tempPredecessorNew = m_sPredecessor;
            //m_sPredecessor 
            while (tempPredecessorOriginal != null)
            {
                tempPredecessorNew = new PartiallySpecifiedState()
            }*/

            if (original.GeneratingAction != null)
                GeneratingAction = original.GeneratingAction.Clone();
            else
                GeneratingAction = null;

            if (original.GeneratingObservation != null)
                GeneratingObservation = original.GeneratingObservation.Clone();
            else
                GeneratingObservation = null;

            Problem = original.Problem;
            if (original.UnderlyingEnvironmentState != null)
                UnderlyingEnvironmentState = original.UnderlyingEnvironmentState.Clone();
            else
                UnderlyingEnvironmentState = null;

            if (Options.ComputeCompletePlanTree)
                m_bsInitialBelief = new BeliefState(original.m_bsInitialBelief);
            else
                m_bsInitialBelief = original.m_bsInitialBelief;
            Time = original.Time;

            if (original.m_cfCNFBelief != null)
                m_cfCNFBelief = new CompoundFormula(original.m_cfCNFBelief);
            else
                m_cfCNFBelief = null;

            if (original.m_lFailureTag != null)
                m_lFailureTag = new List<Predicate>(original.m_lFailureTag);
            else
                m_lFailureTag = null;

            if (original.m_lPreviousTags != null)
                m_lPreviousTags = new List<List<Predicate>>(original.m_lPreviousTags);
            else
                m_lPreviousTags = null;


            if (original.FunctionValues != null) FunctionValues = new Dictionary<string, double>(original.FunctionValues);
            else FunctionValues = null;

            MishapType = original.MishapType;
            MinMishapCount = original.MinMishapCount;
            MaxMishapCount = original.MaxMishapCount;
            MishapCount = original.MishapCount;

            Parents = new List<PartiallySpecifiedState>(original.Parents);
            m_nPlan = new ConditionalPlanTreeNode();//should we copy here?


            SetDeadendList(original.deadEndList);


        }

        private void SetDeadendListII(List<Formula> lOrg)
        {
            deadEndList = new List<Formula>();
            if (lOrg != null)
            {

                foreach (Formula daedend in lOrg)
                {
                    //deadEndList.Add(daedend); 


                    if (daedend is PredicateFormula)
                    {
                        Formula resuceDeadEnd = daedend.Reduce(m_lObserved);
                        PredicateFormula pre_deadEndForm = (PredicateFormula)resuceDeadEnd;

                        Predicate pre_deadEnd = pre_deadEndForm.Predicate;
                        if (pre_deadEnd == Utilities.TRUE_PREDICATE)
                            Debug.Write("*");
                        if (pre_deadEnd != Utilities.FALSE_PREDICATE)
                        {
                            deadEndList.Add(resuceDeadEnd);

                        }




                    }
                    if (daedend is CompoundFormula)
                    {
                        Formula resuceDeadEnd = daedend.Reduce(m_lObserved);
                        if (resuceDeadEnd is PredicateFormula)
                        {
                            PredicateFormula pre_deadEndForm = (PredicateFormula)resuceDeadEnd;

                            Predicate pre_deadEnd = pre_deadEndForm.Predicate;
                            if (pre_deadEnd == Utilities.TRUE_PREDICATE)
                                Debug.Write("*");

                            if (pre_deadEnd != Utilities.FALSE_PREDICATE)
                            {
                                deadEndList.Add(resuceDeadEnd);

                            }

                        }
                        else
                        {

                            deadEndList.Add(resuceDeadEnd);
                        }

                    }





                }
            }
        }



        private void SetDeadendList(List<Formula> lOrg)
        {
            //I don't think that we can revise the list of deadends. Even if some fact in a deadend is false now, it doesn't mean that it wouldn't be true later
            deadEndList = new List<Formula>();
            if (lOrg != null)
            {
                foreach (Formula daedend in lOrg)
                {
                    deadEndList.Add(daedend);
                }
            }
        }

        public PartiallySpecifiedState(BeliefState bs)
        {
            countOfActionFromRoot = 0;
            ID = STATE_COUNT++;



            Problem = bs.Problem;
            m_sPredecessor = null;
            m_lObserved = new HashSet<Predicate>(bs.Observed);
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = bs.UnderlyingEnvironmentState;
            m_bsInitialBelief = bs;
            ChildCount = 0;

            m_lHidden = new HashSet<Predicate>();
            foreach (CompoundFormula cf in bs.Hidden)
            {
                HashSet<Predicate> lCurrent = new HashSet<Predicate>();
                cf.GetAllPredicates(lCurrent);
                foreach (Predicate p in lCurrent)
                {
                    if (p.Negation)
                    {
                        if (!m_lHidden.Contains(p.Negate()))
                            m_lHidden.Add(p.Negate());
                    }
                    else if (!m_lHidden.Contains(p))
                        m_lHidden.Add(p);
                }

            }

            /* as long as there are no non-deterministic effects there is no need to maintain all knowledge
            foreach (Predicate p in bs.Observed)
            {
                if (!Problem.Domain.AlwaysKnown(p))
                    cfBelief.AddOperand(p);
            }
             * */

            FunctionValues = new Dictionary<string, double>();
            foreach (string sFunction in Problem.Domain.Functions)
            {
                FunctionValues[sFunction] = m_bsInitialBelief.FunctionValues[sFunction];
            }

            m_lHistory = new List<string>();
            Parents = new List<PartiallySpecifiedState>();
            m_nPlan = new ConditionalPlanTreeNode();
            m_lDirectlyObserved = new List<Predicate>();

            SetDeadendList(Problem.DeadEndList);

        }
        public PartiallySpecifiedState(PartiallySpecifiedState sPredecessor, Action aGeneratingAction)
        {
            ID = STATE_COUNT++;

            countOfActionFromRoot = sPredecessor.countOfActionFromRoot + 1;
            ChildCount = 0;

            if (Options.ComputeCompletePlanTree)
                m_bsInitialBelief = new BeliefState(sPredecessor.m_bsInitialBelief);
            else
                m_bsInitialBelief = sPredecessor.m_bsInitialBelief;

            Problem = m_bsInitialBelief.Problem;
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = null;
            m_sPredecessor = sPredecessor;

            GeneratingAction = aGeneratingAction;
            m_lObserved = new HashSet<Predicate>(sPredecessor.Observed);
            m_lHidden = new HashSet<Predicate>(sPredecessor.m_lHidden);
            //ForgetPotentialEffects();//Should not be done here, only in the "apply"

            FunctionValues = new Dictionary<string, double>();
            Time = sPredecessor.Time + 1;

            foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                FunctionValues[p.Key] = p.Value;

            m_lHistory = new List<string>(sPredecessor.m_lHistory);
            m_lHistory.Add(ID + ") " + GeneratingAction.Name);

            MishapType = sPredecessor.MishapType;
            MinMishapCount = sPredecessor.MinMishapCount;
            MaxMishapCount = sPredecessor.MaxMishapCount;
            MishapCount = sPredecessor.MishapCount;

            Parents = new List<PartiallySpecifiedState>();
            Parents.Add(sPredecessor);
            m_nPlan = new ConditionalPlanTreeNode();

            m_lDirectlyObserved = new List<Predicate>(sPredecessor.m_lDirectlyObserved);

            SetDeadendList(sPredecessor.deadEndList);

        }

        public void ForgetPotentialEffects()
        {
            HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
            foreach (CompoundFormula cf in GeneratingAction.GetConditions())
            {
                cf.Operands[1].GetAllPredicates(lPossibleEffects);
            }
            foreach (Predicate p in lPossibleEffects)
            {
                Predicate pNegate = p.Negate();
                if (Observed.Contains(p))
                    m_lObserved.Remove(p);
                else if (Observed.Contains(pNegate))
                    m_lObserved.Remove(pNegate);
                m_lHidden.Add(p.Canonical());
            }

        }


        public bool ConsistentWith(Predicate p, bool bCheckingActionPreconditions)
        {
            Predicate pNegate = p.Negate();
            if (Observed.Contains(p))
                return true;
            if (Observed.Contains(pNegate))
                return false;
            if (m_sPredecessor == null)
                return m_bsInitialBelief.ConsistentWith(p, true);
            List<Formula> lRemovingPreconditions = new List<Formula>();
            foreach (CompoundFormula cfCondition in GeneratingAction.GetConditions())
            {
                HashSet<Predicate> lEffects = new HashSet<Predicate>();
                cfCondition.Operands[1].GetAllPredicates(lEffects);
                if (lEffects.Contains(p))
                {
                    if (m_sPredecessor.ConsistentWith(cfCondition.Operands[0], bCheckingActionPreconditions))
                        return true;
                }
                /*
                if (lEffects.Contains(pNegate))
                {
                    //condition removes p
                    //if condition must have happened, then p cannot be true
                    //if the negation of the condition is not consistent, then the condition must have happened
                    //if the negation of the condition is not consistent, p cannot be true
                    Formula fNegate = cfCondition.Operands[0].Negate();
                    bool bCnsistent = m_sPredecessor.ConsistentWith(fNegate);
                    if (!bCnsistent)
                        return false;
                }
                 */
                if (lEffects.Contains(pNegate))
                {
                    lRemovingPreconditions.Add(cfCondition.Operands[0]);
                }
            }
            if (lRemovingPreconditions.Count > 0)
            {
                //if one of the removing conditions must have happened, then p cannot be true
                //if the negation of (or f1 f2 ... fk) is not consistent, then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then p cannot be true
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (Formula f in lRemovingPreconditions)
                    cfAnd.AddOperand(f.Negate());
                bool bConsistent = m_sPredecessor.ConsistentWith(cfAnd, bCheckingActionPreconditions);
                if (!bConsistent)
                    return false;
            }
            return m_sPredecessor.ConsistentWith(p, bCheckingActionPreconditions);
        }

        public bool ConsistentWith(State s)
        {
            foreach (Predicate pState in Observed)
            {
                if (!s.ConsistentWith(pState))
                    return false;
            }
            return true;
        }
        private bool ConsistentWith(Formula fOriginal, bool bCheckingActionPreconditions)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = fOriginal;


            Formula fReduced = null;
            int cRegressions = 0;
            while (pssCurrent.m_sPredecessor != null)
            {
                fReduced = fCurrent.Reduce(pssCurrent.Observed);
                if (fReduced.IsTrue(null))
                    return true;
                if (fReduced.IsFalse(null))
                    return false;

                Formula fToRegress = fReduced;
                if (fToRegress is CompoundFormula)
                {
                    //bool bChanged = false;
                    //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
                }
                if (fToRegress.IsTrue(pssCurrent.Observed))
                    return true;
                if (fToRegress.IsFalse(pssCurrent.Observed))
                    return false;
                Formula fRegressed = fToRegress.Regress(pssCurrent.GeneratingAction, pssCurrent.Observed);
                //Formula fRegressed = fToRegress.Regress(GeneratingAction);
                cRegressions++;

                fCurrent = fRegressed;
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            fReduced = fCurrent.Reduce(pssCurrent.Observed);
            if (fReduced.IsTrue(m_bsInitialBelief.Observed))
                return true;
            if (fReduced.IsFalse(m_bsInitialBelief.Observed))
                return false;
            return m_bsInitialBelief.ConsistentWith(fReduced, bCheckingActionPreconditions);
            //m_bsInitialBelief.ApplyReasoning();

        }
        public bool AddObserved(Predicate p)
        {

            if (p is ParametrizedPredicate)
                throw new NotImplementedException();
            if (p == Utilities.TRUE_PREDICATE)
                return false;


            return AddToObservedList(p);
        }

        private bool AddToObservedList(Predicate p)
        {


#if DEBUG
            if (p.Name != "Choice" && !p.Negation)
            {
                Debug.Assert(UnderlyingEnvironmentState == null || (UnderlyingEnvironmentState.Contains(p)), "Adding a predicate that does not exist");
                if (UnderlyingEnvironmentState != null && !UnderlyingEnvironmentState.Contains(p))
                    Debug.WriteLine("Adding a predicate that does not exist");
            }
#endif
            if (m_lObserved.Contains(p))
                return false;


            Predicate pNegate = p.Negate();
            if (m_lObserved.Contains(pNegate))
                m_lObserved.Remove(pNegate);
            m_lObserved.Add(p);

            if (p.Negation)
                p = pNegate;
            Predicate pCanonical = p.Canonical();
            if (m_lHidden.Contains(pCanonical))
                m_lHidden.Remove(pCanonical);

            return true;
        }

        public bool AddObserved(HashSet<Predicate> l)
        {
            bool bUpdated = false;
            foreach (Predicate p in l)
                if (AddObserved(p))
                    bUpdated = true;
            return bUpdated;
        }

        public HashSet<Predicate> AddObserved(Formula f)
        {

            HashSet<Predicate> hsNew = new HashSet<Predicate>();
            if (f is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)f).Predicate;
                if (AddObserved(p))
                    hsNew.Add(p);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operator == "and")
                    foreach (Formula fSub in cf.Operands)
                        hsNew.UnionWith(AddObserved(fSub));
                else
                {
                    //do nothing here - not adding formulas currently, only certainties
                    //throw new NotImplementedException();
                }
            }
            return hsNew;
        }

        public override bool Equals(object obj)
        {
            if (obj is PartiallySpecifiedState)
            {

                PartiallySpecifiedState bs = (PartiallySpecifiedState)obj;

                if (bs.ClosedState)//this should happen for closed states only
                    return false;

                HashSet<GroundedPredicate> firstObs = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate gp in m_lObserved)
                {
                    if (!gp.ToString().Contains(Utilities.OPTION_PREDICATE) && (!Problem.Domain.AlwaysConstant(gp) || !Problem.Domain.AlwaysKnown(gp)))
                    {
                        firstObs.Add(gp);
                    }
                }
                HashSet<GroundedPredicate> secondObs = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate gp in bs.m_lObserved)
                {
                    if (!gp.ToString().Contains(Utilities.OPTION_PREDICATE) && (!Problem.Domain.AlwaysConstant(gp) || !Problem.Domain.AlwaysKnown(gp)))
                    {
                        secondObs.Add(gp);
                    }
                }
                if (secondObs.Count != firstObs.Count)
                    return false;
                foreach (Predicate p in secondObs)
                    if (!firstObs.Contains(p))
                        return false;
                return true;
            }
            return false;
        }
        /* public override bool Equals(object obj)
         {
             if (obj is PartiallySpecifiedState)
             {
                 PartiallySpecifiedState bs = (PartiallySpecifiedState)obj;

                 if (bs.m_lObserved.Count != m_lObserved.Count)
                     return false;
                 foreach (Predicate p in bs.m_lObserved)
                     if (!m_lObserved.Contains(p))
                         return false;
                 return true;
             }
             return false;
         }*/
        public bool Contains(Formula f)
        {
            return f.ContainedIn(m_lObserved, true);
        }

        public virtual PartiallySpecifiedState Clone()
        {
            PartiallySpecifiedState bsClone = new PartiallySpecifiedState(this);
            bsClone.m_bsInitialBelief = new BeliefState(m_bsInitialBelief);
            /*
            PartiallySpecifiedState bsTemp = bsClone;
            while (bsTemp.m_sPredecessor != null)
            {
                bsTemp.m_sPredecessor = new PartiallySpecifiedState(bsTemp.m_sPredecessor);
                bsTemp = bsTemp.m_sPredecessor;
                bsTemp.m_bsInitialBelief = bsClone.m_bsInitialBelief;
            }
             * */
            return bsClone;
        }

        public bool IsApplicable(string sActionName)
        {
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return false;
            return IsApplicable(a);
        }

        private bool IsApplicable(Action a)
        {
            if (a.Preconditions == null)
                return true;
            m_bsInitialBelief.MaintainProblematicTag = true;
            Formula fReduced = a.Preconditions.Reduce(m_lObserved);

            if (fReduced.IsTrue(m_lObserved))
                return true;
            if (fReduced.IsFalse(m_lObserved))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, true))
            {
                return false;
            }
            AddObserved(a.Preconditions);

            return true;
        }

        public DeadEndExistence IsDeadEndState()
        {
            List<Formula> lDeadends = null;
            return IsDeadEndExistenceAll(out lDeadends);
        }



        public DeadEndExistence IsDeadEndExistenceAll(out List<Formula> lDeadends)
        {
            lDeadends = new List<Formula>();
            if (deadEndList == null || deadEndList.Count == 0)
            {
                return DeadEndExistence.DeadEndFalse;
            }
            foreach (Formula fDeadend in deadEndList)
            {
                //bool bPossibleNot = m_bsInitialBelief.ConsistentWith(fDeadend.Negate(), false);
                bool bPossibleNot = ConsistentWith(fDeadend.Negate(), false);
                if (!bPossibleNot)
                {
                    lDeadends.Add(fDeadend);// in this case we want the full deadend for the closed state mechanism
                    return DeadEndExistence.DeadEndTrue;
                }
            }

            foreach (Formula fDeadend in deadEndList)
            {
                //bool bPossible = m_bsInitialBelief.ConsistentWith(fDeadend, false);
                bool bPossible = ConsistentWith(fDeadend, false);
                if (bPossible)
                {
                    lDeadends.Add(fDeadend.Reduce(m_lObserved)); // here we want the reduced deadend for the deadend sensing plan
                }
            }

            CompoundFormula cfAndNot = new CompoundFormula("and");
            foreach (Formula fDeadend in lDeadends)
            {
                cfAndNot.AddOperand(fDeadend.Negate());
            }
            bool bAllFalse = ConsistentWith(cfAndNot, false);
            //bool bAllFalse = m_bsInitialBelief.ConsistentWith(cfAndNot, false);
            if (!bAllFalse)
                return DeadEndExistence.DeadEndTrue;


            if (lDeadends.Count > 0)
                return DeadEndExistence.MaybeDeadEnd;


            return DeadEndExistence.DeadEndFalse;
        }




        public DeadEndExistence IsDeadEndExistenceAllIII(out List<Formula> lDeadends)
        {
            lDeadends = new List<Formula>();
            if (deadEndList == null)
            {
                return DeadEndExistence.DeadEndFalse;
            }
            List<Formula> DeadEndListCopyUpdate = null;
            bool deadendmaybe = false;
            bool copyList = false;
            List<Formula> DeadEndListCopy = new List<Formula>(deadEndList);
            List<Formula> DeadEndListCopy2 = new List<Formula>(deadEndList);
            foreach (Formula daedendTmp in deadEndList)
            {
                if (daedendTmp.IsTrue(m_lObserved))
                {
                    foreach (Formula daedendTmp2 in deadEndList)
                    {
                        if (daedendTmp2.IsTrue(m_lObserved))
                        {
                            lDeadends.Add(daedendTmp2);
                        }
                    }
                    return DeadEndExistence.DeadEndTrue;
                }
            }

            foreach (Formula fDeadend in deadEndList)
            {
                if (fDeadend is PredicateFormula pf)
                {
                    if (Problem.Domain.AlwaysConstant(pf.Predicate))
                    {
                        bool bNotPossible = ConsistentWith(pf.Negate(), false);
                        if (!bNotPossible)
                        {
                            lDeadends.Add(pf);
                        }
                    }
                }
                else
                {
                    CompoundFormula cf = (CompoundFormula)fDeadend;
                    if (cf.Operator == "and")
                    {
                        CompoundFormula cfConstant = new CompoundFormula("and");
                        foreach (PredicateFormula pfSub in cf.Operands)
                        {
                            if (Problem.Domain.AlwaysConstant(pfSub.Predicate))
                            {
                                cfConstant.AddOperand(pfSub);
                            }
                        }
                        bool bPossible = ConsistentWith(cfConstant, false);
                        if (bPossible)
                        {
                            //ignoring the non-constants, because they may occur later. However, if we refute the constants, then the deadend will not occur.
                            lDeadends.Add(cfConstant);
                        }
                    }
                    else
                    {
                        throw new NotImplementedException("Not supporting disjunctive deadends: " + cf);
                    }
                }
            }

            if (lDeadends.Count > 0)
                return DeadEndExistence.MaybeDeadEnd;


            return DeadEndExistence.DeadEndFalse;
        }



        public DeadEndExistence IsDeadEndExistenceAllII(out List<Formula> lDeadends)
        {
            lDeadends = new List<Formula>();
            //bool deadEndExist = false; 
            if (deadEndList == null)
            {
                return DeadEndExistence.DeadEndFalse;

            }
            List<Formula> DeadEndListCopyUpdate = null;
            bool deadendmaybe = false;
            bool copyList = false;
            List<Formula> DeadEndListCopy = new List<Formula>(deadEndList);
            List<Formula> DeadEndListCopy2 = new List<Formula>(deadEndList);
            foreach (Formula daedendTmp in DeadEndListCopy)
            {
                if (daedendTmp.IsTrue(m_lObserved))
                {
                    // {
                    //
                    //foreach (Formula daedendTmpprob in Problem.deadEndList)
                    //{
                    //if (daedendTmpprob.ContainsCondition())


                    //                    }
                    //deadEnd = daedendTmp;

                    foreach (Formula daedendTmp2 in Problem.DeadEndList)
                    {
                        if (daedendTmp2.IsTrue(m_lObserved))
                        {
                            lDeadends.Add(daedendTmp2);
                        }
                        /*
                        if (daedendTmp is PredicateFormula)
                        {
                            HashSet<Predicate> predictsList = new HashSet<Predicate>();
                            daedendTmp2.GetAllPredicates(predictsList);

                            PredicateFormula pf = (PredicateFormula)daedendTmp;

                            foreach (Predicate pred in predictsList)
                            {
                                if (pred.Equals(pf.Predicate))
                                {
                                    lDeadends.Add(daedendTmp2);
                                    return DeadEndExistence.DeadEndTrue;
                                }

                            }
                        }
                        else
                        {
                            lDeadends.Add(daedendTmp);
                            return DeadEndExistence.DeadEndTrue;
                        }
                        */
                    }
                    return DeadEndExistence.DeadEndTrue;
                }
                /*
                Formula deadEndNegate = daedendTmp.Negate();
                if (deadEndNegate.IsTrue(m_lObserved))
                {
                    deadEndList.Remove(daedendTmp);
                    continue;
                }
*/
                Formula reduceDeadEnd = daedendTmp.Reduce(m_lObserved);
                //if (daedendTmp.IsTrue(m_lObserved) || reduceDeadEnd.IsTrue(m_lObserved))




                /*
                if (reduceDeadEnd.Equals(daedendTmp) == false)
                {

                    DeadEndListCopyUpdate = new List<Formula>();
                    DeadEndListCopyUpdate.Add(reduceDeadEnd);
                    foreach (Formula daedendTmp2 in DeadEndListCopy2)
                    {
                        if (daedendTmp.Equals(daedendTmp2) == false )
                        {

                            DeadEndListCopyUpdate.Add(daedendTmp2); 
                        }

                    }
                    copyList = true; 
                    
                       // deadEndList.Remove(daedendTmp);
                    //deadEndList.Add(reduceDeadEnd);


                }
                */

                //Debug.WriteLine("maybe dead end!!!");
                //Debug.WriteLine(reduceDeadEnd);
                //Debug.WriteLine(daedendTmp);
                //Debug.WriteLine(this);
                deadendmaybe = true;
                lDeadends.Add(reduceDeadEnd);
                //deadEnd = daedendTmp;
            }

            if (deadendmaybe)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                foreach (Formula f in lDeadends)
                {
                    cfOr.AddOperand(f);
                }
                Formula fSimplifiedOr = cfOr.Simplify();
                bool bPossiblyNotDeadend = ConsistentWith(fSimplifiedOr.Negate(), false);

                if (!bPossiblyNotDeadend)
                {
                    return DeadEndExistence.DeadEndTrue;
                }

                //if (copyList)
                //deadEndList = DeadEndListCopyUpdate;
                return DeadEndExistence.MaybeDeadEnd;
            }

            return DeadEndExistence.DeadEndFalse;
        }

        public List<Formula> returnListOfMaybeDeadEnd()
        {
            List<Formula> deadEndsReturn = new List<Formula>();
            foreach (Formula daedend in Problem.DeadEndList)
            {
                if (daedend.IsTrue(m_lObserved) == false && daedend.IsFalse(m_lObserved) == false)
                    deadEndsReturn.Add(daedend);
                Debug.WriteLine("maybe dead end");
                Debug.WriteLine(daedend);
                Debug.WriteLine(this);
                //for now i return for maybe deadend true that i can use it. 
            }

            return deadEndsReturn;

        }


        public List<Formula> returnListOfDeadEnd()
        {
            List<Formula> deadEndsReturn = new List<Formula>();
            foreach (Formula daedend in Problem.DeadEndList)
            {
                if (daedend.IsTrue(m_lObserved))
                    deadEndsReturn.Add(daedend);
                Debug.WriteLine("dead end!!!");
                Debug.WriteLine(daedend);
                Debug.WriteLine(this);
                //for now i return for maybe deadend true that i can use it. 
            }

            return deadEndsReturn;

        }

        public PartiallySpecifiedState Apply(string sActionName, out Formula fObserve)
        {
            fObserve = null;
            string sRevisedActionName = sActionName.Replace(Utilities.DELIMITER_CHAR, " ");
            string[] aName = sRevisedActionName.Split(' ');
            Action a = Problem.Domain.GroundActionByName(aName);
            if (a == null)
            {
                return null;
            }
            PartiallySpecifiedState pssNext = Apply(a, out fObserve);
            return pssNext;
        }

        public PartiallySpecifiedState Apply(Action a, out Formula fObserve)
        {
            return Apply(a, out fObserve, false);
        }

        public static TimeSpan tsPre = new TimeSpan(), tsEffects = new TimeSpan(), tsObs = new TimeSpan();



        public void ApplyOffline(Action a, out bool bPreconditionFailure, out Formula fObserve, out PartiallySpecifiedState psTrueState,
            out PartiallySpecifiedState psFalseState, bool bAllowRedundantObservations = false)
        {
            psTrueState = null;
            psFalseState = null;
            fObserve = null;
            bPreconditionFailure = false;


            if (a.Observe != null && a.Effects != null)
                throw new NotImplementedException();

            a = a.RemoveNonDeterministicEffects(m_bsInitialBelief);

            Action aTag = a.ApplyObserved(m_lObserved); //for removing all generaly known items from the computations.
            a = aTag;

            Formula fPreconditions = a.Preconditions;
            if (fPreconditions != null && !IsApplicable(a))
            {
                bPreconditionFailure = true;
                return;
            }
            PartiallySpecifiedState bsNew = new PartiallySpecifiedState(this, a);


            ChildCount = 1;
            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());
                    bsNew.ApplyKnowledgeLoss(lApplicableConditions);
                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(m_lObserved, lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (Predicate p in lRemoveEffects)
                        bsNew.AddEffect(p);
                    foreach (Predicate p in lAddEffects)
                        bsNew.AddEffect(p);
                    //bsNew.UpdateHidden(a, m_lObserved);
                    bsNew.UpdateHidden();
                }
                else
                {
                    bsNew.AddEffects(a.Effects);
                }
                foreach (Predicate pNonDet in a.NonDeterministicEffects)
                {
                    bsNew.m_lObserved.Remove(pNonDet);
                    bsNew.m_lHidden.Add(pNonDet.Canonical());
                }
            }
            if (a.Observe != null)
            {
                Predicate pObserve = a.Observe.GetAllPredicates().First();
                if (m_lObserved.Contains(pObserve) || m_lObserved.Contains(pObserve.Negate()))
                {
                    if (!bAllowRedundantObservations)
                    {
                        psTrueState = null;
                        psFalseState = null;
                        return;
                    }
                }

                PartiallySpecifiedState bsTrue = bsNew;
                PartiallySpecifiedState bsFalse = bsNew.Clone();
                bsTrue.GeneratingObservation = a.Observe;
                bsFalse.GeneratingObservation = a.Observe.Negate();

                bool bConsistentWithTrue = bsTrue.ConsistentWith(bsTrue.GeneratingObservation, false);
                bool bConsistentWithFalse = bsFalse.ConsistentWith(bsFalse.GeneratingObservation, false);

                if (a.Effects == null)
                {
                    if (!bConsistentWithTrue || !bConsistentWithFalse)
                    {
                        //if only one observation is possible, make it a part of the state
                        if (bConsistentWithTrue)
                            AddObserved(bsTrue.GeneratingObservation);
                        if (bConsistentWithFalse)
                            AddObserved(bsFalse.GeneratingObservation);

                        if (!bAllowRedundantObservations)
                        {
                            psTrueState = null;
                            psFalseState = null;
                            return;
                        }
                    }
                }



                ChildCount = 0;


                if (bConsistentWithTrue)
                {
                    HashSet<int> hsModifiedTrue = bsTrue.m_bsInitialBelief.ReviseInitialBelief(bsTrue.GeneratingObservation, bsTrue);
                    //this is after a split - cannot propagate backwards the observation
                    /*
                  if (hsModifiedTrue.Count > 0)
                  {
                      bsTrue.PropogateObservedPredicates();
                  }
                    */
                    bsTrue.AddObserved(a.Observe);
                    psTrueState = bsTrue;
                    ChildCount++;
                }
                else
                    psTrueState = null;

                if (bConsistentWithFalse)
                {
                    HashSet<int> hsModifiedFalse = bsFalse.m_bsInitialBelief.ReviseInitialBelief(bsFalse.GeneratingObservation, bsFalse);
                    //this is after a split - cannot propagate backwards the observation
                    /*
                    if (hsModifiedFalse.Count > 0)
                  {
                      bsFalse.PropogateObservedPredicates();
                  }
                    */
                    bsFalse.AddObserved(a.Observe.Negate());

                    psFalseState = bsFalse;
                    ChildCount++;
                }
                else
                    psFalseState = null;
            }
            else
                psTrueState = bsNew;



        }

        public void AddCurrentToDeadendTags()
        {
            m_bsInitialBelief.AddCurrentToDeadendTags();
        }

        public void SetProblematicTagToCurrent()
        {
            m_bsInitialBelief.SetProblematicTagToCurrent();
        }

        public void FindEffects(HashSet<Predicate> ans, Formula f, bool flag)
        {
            try
            {
                if (f != null)
                {
                    if (f is PredicateFormula)
                    {
                        if (flag)
                        {
                            PredicateFormula pf = (PredicateFormula)f;
                            ans.Add(pf.Predicate);
                        }
                    }
                    else
                    {
                        CompoundFormula cf = (CompoundFormula)f;
                        if (cf.Operator.Equals("and"))
                        {
                            foreach (Formula subExp in cf.Operands)
                            {
                                FindEffects(ans, subExp, flag);
                            }
                        }
                        else
                        {
                            if (cf.Operator.Equals("when"))
                            {
                                if (!cf.Operands[0].IsTrue(m_lObserved))
                                    FindEffects(ans, cf.Operands[1], true);
                            }
                            else
                            {
                                if (cf.Operator.Equals("oneof"))
                                {
                                    // if (!cf.Operands[0].IsTrue(m_lObserved))
                                    FindEffects(ans, cf.Operands[1], true);
                                }
                            }
                        }

                    }
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine(ex.ToString());
            }
        }

        PartiallySpecifiedState FirstObsChild = null;
        PartiallySpecifiedState SecondObsChild = null;
        public void ApplyOffline(string sActionName, out Action a, out bool bPreconditionFailure, out Formula fObserve, out PartiallySpecifiedState psTrueState, out PartiallySpecifiedState psFalseState)
        {
            psTrueState = null;
            psFalseState = null;
            fObserve = null;
            bPreconditionFailure = false;
            string sRevisedActionName = sActionName.Replace(Utilities.DELIMITER_CHAR, " ");
            string[] aName = sRevisedActionName.Split(' ');
            a = Problem.Domain.GroundActionByName(aName);
            if (a == null || a is ParametrizedAction)
                return;

            ApplyOffline(a, out bPreconditionFailure, out fObserve, out psTrueState, out psFalseState);

            if (bPreconditionFailure)
                return;

            if (psTrueState != null && psFalseState == null)
            {
                FirstObsChild = psTrueState;
            }

            if (psTrueState == null && psFalseState != null)
            {
                FirstObsChild = psFalseState;
            }

            if (psTrueState != null && psFalseState != null)
            {
                FirstObsChild = psTrueState;
                SecondObsChild = psFalseState;
            }

            HashSet<Predicate> newEff = new HashSet<Predicate>();
            if (a.Effects != null)
            {
                FindEffects(newEff, a.Effects, false);
            }




            if (psTrueState != null)
            {
                psTrueState.tmpId = this.tmpId;
                if (mayChanged != null)
                {
                    psTrueState.mayChanged = new HashSet<Predicate>();
                }

                if (ActionsWithConditionalEffect != null)
                {
                    psTrueState.ActionsWithConditionalEffect = new HashSet<Action>();
                }
            }


            if (psFalseState != null)
            {
                psFalseState.tmpId = this.tmpId;
                if (mayChanged != null)
                {
                    psFalseState.mayChanged = new HashSet<Predicate>();
                }

                if (ActionsWithConditionalEffect != null)
                {
                    psFalseState.ActionsWithConditionalEffect = new HashSet<Action>();
                }
            }


            List<Predicate> NonDeterministicEffects = a.GetNonDeterministicEffects();
            List<PartiallySpecifiedState> workingSet = new List<PartiallySpecifiedState>();

            if (psFalseState != null)
            {
                workingSet.Add(psFalseState);
            }

            if (psTrueState != null)
            {
                workingSet.Add(psTrueState);
            }
            HashSet<Predicate> conEff = new HashSet<Predicate>();
            if (a.Effects != null)
            {
                FindEffects(conEff, a.Effects, false);
            }
            foreach (PartiallySpecifiedState bsNew in workingSet)
            {
                if (NonDeterministicEffects != null && NonDeterministicEffects.Count > 0)
                {
                    foreach (GroundedPredicate gp in NonDeterministicEffects)
                    {
                        bsNew.m_lObserved.Remove(gp);
                        bsNew.m_lHidden.Add(gp);
                    }
                }
                bsNew.countOfActionFromRoot = countOfActionFromRoot + 1;
                if (regressionFormula == null)
                {
                    if (conEff.Count > 0)
                    {
                        bsNew.regressionFormula = new Dictionary<GroundedPredicate, Formula>();
                        foreach (GroundedPredicate gp in conEff)
                        {
                            bsNew.regressionFormula.Add(gp, null);
                        }
                    }
                }
                else
                {
                    bsNew.regressionFormula = new Dictionary<GroundedPredicate, Formula>(regressionFormula);
                    if (conEff.Count > 0)
                    {
                        foreach (GroundedPredicate gp in conEff)
                        {
                            if (!bsNew.regressionFormula.ContainsKey(gp))
                                bsNew.regressionFormula.Add(gp, null);
                            else
                                bsNew.regressionFormula[gp] = null;
                        }
                    }
                }
            }

        }
        private PartiallySpecifiedState Apply(Action aOrg, out Formula fObserve, bool bPropogateOnly)
        {
            //Debug.WriteLine("Executing " + a.Name);
            fObserve = null;
            if (aOrg is ParametrizedAction)
                return null;

            DateTime dtStart = DateTime.Now;

            Action a = aOrg.ApplyObserved(m_lObserved);

            //no need to check pre during propogation - they were already confirmed the first time
            if (!bPropogateOnly && a.Preconditions != null && !IsApplicable(a))
                return null;

            a.ComputeRegressions();

            tsPre += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            State sNew = null;
            if (!bPropogateOnly && UnderlyingEnvironmentState != null)
                sNew = UnderlyingEnvironmentState.Apply(a);

            CompoundFormula cfAndChoices = null;
            if (!bPropogateOnly && a.ContainsNonDeterministicEffect)
            {
                a = a.RemoveNonDeterminism(Time, out cfAndChoices);
            }

            PartiallySpecifiedState bsNew = new PartiallySpecifiedState(this, a);
            if (sNew != null)
            {
                bsNew.UnderlyingEnvironmentState = sNew;
                if (!bPropogateOnly && bsNew.Time != sNew.Time)
                    Debug.WriteLine("BUGBUG");

            }

            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());
                    bsNew.ApplyKnowledgeLoss(lApplicableConditions);
                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(m_lObserved, lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (Predicate p in lRemoveEffects)
                        bsNew.AddEffect(p);
                    foreach (Predicate p in lAddEffects)
                        bsNew.AddEffect(p);
                    //bsNew.UpdateHidden(a, m_lObserved);
                    bsNew.UpdateHidden();
                }
                else
                {
                    bsNew.AddEffects(a.Effects);
                }
            }

            //if(m_sPredecessor != null)//the first one holds all knowns, to avoid propogation from the initial belief
            //   RemoveDuplicateObserved(bsNew.m_lObserved);//if p is true at t+1 and p is true at t, there is no point in maintaining the copy at t 

            tsEffects += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            if (!bPropogateOnly && a.Observe != null)
            {
                //first applying the action (effects) and then observing
                fObserve = bsNew.UnderlyingEnvironmentState.Observe(a.Observe);

                bsNew.GeneratingObservation = fObserve;
                bsNew.AddObserved(fObserve);

                /*
                if (ReviseInitialBelief(fObserve))
                    bsNew.PropogateObservedPredicates();
                 * */
                HashSet<int> hsModified = m_bsInitialBelief.ReviseInitialBelief(fObserve, this);
                if (hsModified.Count > 0)
                {
                    if (!Options.OptimizeMemoryConsumption)
                        bsNew.PropogateObservedPredicates();
                }

            }

            tsObs += DateTime.Now - dtStart;


            if (bsNew != null && cfAndChoices != null)
                m_bsInitialBelief.AddInitialStateFormula(cfAndChoices);

            //if (!bPropogateOnly && bsNew.Time != sNew.Time)
            //    Debug.WriteLine("BUGBUG");

            return bsNew;
        }

        private void RemoveDuplicateObserved(HashSet<Predicate> hObservedAtNextStep)
        {
            HashSet<Predicate> hsFiltered = new HashSet<Predicate>();
            foreach (Predicate p in Observed)
            {
                if (!hObservedAtNextStep.Contains(p))
                    hsFiltered.Add(p);
            }
            m_lObserved = hsFiltered;
        }

        private void UpdateHidden()
        {
            //bugbug; // there must be a better implementation!
            return;

            //we handle here only a very special case, where p->~p, and we don't have q->p. In this case either ~p was true before the action, or p was true and now we have ~p.
            //there is a more general case where when either p or ~p was correct before the action, q should hold after it, but we do not handle it here.


            //we need to check every condition that has pHidden as an effect
            List<Predicate> lPreviouslyHidden = new List<Predicate>(m_lHidden);



            foreach (Predicate pHidden in lPreviouslyHidden)
            {
                Predicate pNegateHidden = pHidden.Negate();

                List<CompoundFormula> lAddsP = new List<CompoundFormula>(), lRemovesP = new List<CompoundFormula>();
                foreach (CompoundFormula cf in GeneratingAction.GetConditions())
                {
                    HashSet<Predicate> lEffects = cf.Operands[1].GetAllPredicates();
                    if (lEffects.Contains(pHidden))
                    {
                        lAddsP.Add(cf);
                        break;
                    }
                    else if (lEffects.Contains(pNegateHidden))
                        lRemovesP.Add(cf);
                }

                //handling here only the case: ~p->p, there is an opposite case p->~p, but there is no domain that uses that, so we don't implement it.
                if (lAddsP.Count > 0)
                {
                    //nothing to check here - p could be added, so we cannot conclude that ~p holds afterwards
                    continue;
                }
                if (lRemovesP.Count > 0)
                {
                    List<Predicate> lObserved = new List<Predicate>();
                    lObserved.Add(pHidden);
                    foreach (CompoundFormula cf in lRemovesP)
                    {
                        if (cf.Operands[0].IsTrue(lObserved))//if p then ~p, so either ~p before the action, or p and then ~p after the action
                        {
                            AddObserved(pNegateHidden);
                            break;
                        }
                    }
                }
            }

        }

        private List<CompoundFormula> ApplyKnown(List<CompoundFormula> lConditions)
        {
            List<CompoundFormula> lClean = new List<CompoundFormula>();
            foreach (CompoundFormula cfCondition in lConditions)
            {
                if (!cfCondition.Operands[0].IsTrue(m_lObserved))//in this case thre is no reasoning - conditional effects are known
                {
                    if (!cfCondition.Operands[0].IsFalse(m_lObserved))//in this case the rule does not apply, so no valuable reasoning
                    {
                        CompoundFormula cfClean = new CompoundFormula("when");
                        if ((cfCondition.Operands[0]) is CompoundFormula)
                            cfClean.AddOperand(((CompoundFormula)cfCondition.Operands[0]).RemovePredicates(m_lObserved));
                        else
                        {
                            PredicateFormula pf = (PredicateFormula)(cfCondition.Operands[0]);
                            if (!m_lObserved.Contains(pf.Predicate))
                                cfClean.AddOperand(pf);
                            else
                                cfClean.AddOperand(new CompoundFormula("and"));
                        }
                        cfClean.AddOperand(cfCondition.Operands[1]);
                        lClean.Add(cfClean);
                    }
                }
            }
            return lClean;
        }


        //forget effects only if they currently have a known value and that value might change
        private void ApplyKnowledgeLoss(List<CompoundFormula> lConditions)
        {
            HashSet<Predicate> lAllEffectPredicates = new HashSet<Predicate>();
            foreach (CompoundFormula cfCondition in lConditions)
            {//for now assuming that when clause is only a simple conjunction
                lAllEffectPredicates.UnionWith(cfCondition.Operands[1].GetAllPredicates());
            }
            foreach (Predicate pEffect in lAllEffectPredicates)
            {
                Predicate pNegate = pEffect.Negate();
                if (m_lObserved.Contains(pNegate))
                {
                    AddHidden(pNegate);
                }
            }
        }

        private void AddHidden(Predicate pHidden)
        {
            m_lObserved.Remove(pHidden);
            m_lHidden.Add(pHidden.Canonical());
        }
        private void AddHidden(Formula f)
        {
            if (f is PredicateFormula)
                AddHidden(((PredicateFormula)f).Predicate);
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                foreach (Formula fSub in cf.Operands)
                    AddHidden(fSub);
            }
        }

        public Formula RegressObservation(Formula f)
        {
            /* There is no point in adding the observation, because it was already regressed
            CompoundFormula fWithObservation = new CompoundFormula("and");
            fWithObservation.AddOperand(f);
            if (GeneratingObservation != null)
                fWithObservation.AddOperand(GeneratingObservation);
            Formula fReduced = fWithObservation.Reduce(Observed);
             */
            Formula fReduced = f.Reduce(Observed);
            Formula fToRegress = fReduced;
            if (fToRegress is CompoundFormula)
            {
                bool bChanged = false;
                //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged).Simplify();
            }
            if (fToRegress.IsTrue(null))
                return fToRegress;
            if (fToRegress.IsFalse(null))
                Debug.Assert(false);
            if (GeneratingAction.HasConditionalEffects)
            {
                Formula fRegressed = fToRegress.Regress(GeneratingAction, Observed);
                return fRegressed;
            }
            else
                return fToRegress;
        }
        /*
                //returns true if new things were learned
                private bool ReviseInitialBelief(Formula fObserve)
                {
                    Formula fReduced = fObserve.Reduce(Observed);

                    Formula fToRegress = fReduced;
                    if (fToRegress is CompoundFormula)
                    {
                        bool bChanged = false;
                        fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
                    }
                    if (fToRegress.IsTrue(Observed))
                        return false;
                    if (fToRegress.IsFalse(Observed))
                        Debug.Assert(false);
                    if (m_sPredecessor != null)
                    {
                        Formula fRegressed = fToRegress.Regress(GeneratingAction, Observed);
                        bool bPredecessorUpdated = m_sPredecessor.ReviseInitialBelief(fRegressed);
                        if (bPredecessorUpdated)
                        {
                            bool bCurrentUpdated = PropogateObservedPredicates();
                            return bCurrentUpdated;
                        }
                        return false;
                    }
                    else
                    {
                        m_lModifiedClauses = m_bsInitialBelief.AddReasoningFormula(fReduced);
                        HashSet<Predicate> lLearned = ApplyReasoning();
                        return lLearned.Count > 0;
                    }
                }
        */
        //returns true if new things were propogated
        public bool PropogateObservedPredicates()
        {

            Formula fObserve = null;

            GeneratingAction.IdentifyActivatedOptions(m_sPredecessor.Observed, Observed);


            PartiallySpecifiedState pssAux = m_sPredecessor.Apply(GeneratingAction, out fObserve, true);
            if (pssAux.m_lObserved.Count == m_lObserved.Count)
                return false;
            foreach (Predicate pObserve in pssAux.Observed)
            {
                AddObserved(pObserve);
            }
            /*
            if (m_sPredecessor.Observed.Count() > Observed.Count() + 4)
            {
                foreach (Predicate p in m_sPredecessor.Observed)
                    if (!m_lObserved.Contains(p))
                        Debug.WriteLine(p);
                Debug.WriteLine("*");
            }
             * */
            return true;
        }


        //returns true if new things were propogated
        public HashSet<Predicate> PropogateObservedPredicates(HashSet<Predicate> lNewPredicates)
        {
            HashSet<Predicate> hsNextNewPredicates = new HashSet<Predicate>();

            GeneratingAction.IdentifyActivatedOptions(m_sPredecessor.Observed, Observed);

            if (GeneratingAction.Effects != null)
            {

                Action aRevised = GeneratingAction.ApplyObserved(lNewPredicates);
                foreach (Predicate p in aRevised.GetMandatoryEffects())
                {
                    if (!m_lObserved.Contains(p))
                    {
                        hsNextNewPredicates.Add(p);
                        if (!Options.OptimizeMemoryConsumption && !Options.ComputeCompletePlanTree)
                            AddObserved(p);
                    }
                }

                //these are optional effects, so we are not sure whether the newly learned predicate will hold after the action, so we cannot propogate the knowledge - a forgetting mechanism
                HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
                foreach (CompoundFormula cf in aRevised.GetConditions())
                {
                    cf.Operands[1].GetAllPredicates(lPossibleEffects);
                }
                foreach (Predicate p in lPossibleEffects)
                {
                    Predicate pNegate = p.Negate();
                    if (lNewPredicates.Contains(p))
                        lNewPredicates.Remove(p);
                    else if (lNewPredicates.Contains(pNegate))
                        lNewPredicates.Remove(pNegate);

                }
                if (!Options.ComputeCompletePlanTree)
                    GeneratingAction = aRevised;
            }


            //pretty sure that this is correct - for every new fact that was learned for the previous state, if it is not contradicted by the action, then it shold be added
            foreach (Predicate p in lNewPredicates)
            {
                if (!Observed.Contains(p.Negate()))
                {
                    if (!Options.OptimizeMemoryConsumption && !Options.ComputeCompletePlanTree)
                        AddObserved(p);
                    hsNextNewPredicates.Add(p);
                }
            }

            return hsNextNewPredicates;
        }

        public bool AlreadyVisited(Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisitedStates)
        {
            if (!Problem.Domain.ContainsNonDeterministicActions)
                return false;
            if (GeneratingObservation != null)
                return false;//this requires a special case that I have no desire to handle
            if (dVisitedStates.ContainsKey(this))
            {
                PartiallySpecifiedState sourcePs = dVisitedStates[this];
                bool bLoopDetected = DetectInfiniteLoopComplete(sourcePs, Predecessor);
                if (bLoopDetected)
                    return false;
                dVisitedStates[this].AddParent(Predecessor);
                //BUGBUG - assuming here that the generating action was not an observation action
                if (GeneratingAction.Observe != null)
                    return false;
                PartiallySpecifiedState psIdentical = dVisitedStates[this];
                Predecessor.Plan.SingleChild = psIdentical.Plan;
                Predecessor.Plan.Action = GeneratingAction;

                return true;
            }
            return false;
        }
        public void MarkVisited(Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisitedStates)
        {
            if (Problem.Domain.ContainsNonDeterministicActions)
            {
                dVisitedStates[new PartiallySpecifiedState(this)] = this;
                mayChanged = new HashSet<Predicate>();
                ActionsWithConditionalEffect = new HashSet<Action>();
            }
        }

        //returns true if new things were learned
        public HashSet<Predicate> ApplyReasoning()
        {
            /* not really doing here anything - is this a bug?
            List<Predicate> lHidden = new List<Predicate>();
            foreach (Predicate p in m_bsInitialBelief.Unknown)
            {
                if (p.Negation)
                {
                    if (!lHidden.Contains(p.Negate()))
                        lHidden.Add(p.Negate());
                }
                else
                {
                    if (!lHidden.Contains(p))
                        lHidden.Add(p);
                }
             
            }
             */
            HashSet<Predicate> lLearned = new HashSet<Predicate>();
            if (m_bsInitialBelief.Observed.Count() > Observed.Count())
            {
                foreach (Predicate p in m_bsInitialBelief.Observed)
                    if (AddObserved(p))
                        lLearned.Add(p);
            }
            return lLearned;
        }

        private void AddEffect(Predicate pEffect)
        {
            if (Problem.Domain.IsFunctionExpression(pEffect.Name))
            {
                GroundedPredicate gpIncreaseDecrease = (GroundedPredicate)pEffect;
                double dPreviousValue = m_sPredecessor.FunctionValues[gpIncreaseDecrease.Constants[0].Name];
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
            else if (!Observed.Contains(pEffect))
            {
                Predicate pNegateEffect = pEffect.Negate();
                if (Observed.Contains(pNegateEffect))
                {
                    //Debug.WriteLine("Removing " + pNegateEffect);
                    m_lObserved.Remove(pNegateEffect);
                }
                //Debug.WriteLine("Adding " + pEffect);
                AddObserved(pEffect);
            }
        }

        public bool DetectInfiniteLoop(PartiallySpecifiedState pss)
        {
            PartiallySpecifiedState pssCurrent = pss;
            bool bInfiniteLoopDetected = true;
            while (pssCurrent != null)
            {
                if (pssCurrent.ID == ID)
                    break;
                if (pssCurrent.GeneratingAction != null && pssCurrent.GeneratingAction.Observe != null)
                    bInfiniteLoopDetected = false;
                pssCurrent = pssCurrent.Predecessor;
            }
            if (pssCurrent != null && pssCurrent.ID == ID && bInfiniteLoopDetected)
                return true;
            return false;

        }
        public bool DetectInfiniteLoopComplete(PartiallySpecifiedState sourcePs, PartiallySpecifiedState descendantPs)
        {
            if (sourcePs.ID == descendantPs.ID)
                return true;
            else
            {
                if (sourcePs.FirstObsChild != null && sourcePs.SecondObsChild != null)
                    return (DetectInfiniteLoopComplete(sourcePs.FirstObsChild, descendantPs) && DetectInfiniteLoopComplete(sourcePs.SecondObsChild, descendantPs));
                else
                {
                    if (sourcePs.FirstObsChild != null)
                        return (DetectInfiniteLoopComplete(sourcePs.FirstObsChild, descendantPs));
                    else
                    {
                        if (sourcePs.SecondObsChild != null)
                            return (DetectInfiniteLoopComplete(sourcePs.SecondObsChild, descendantPs));
                        else
                        {
                            return false;
                        }
                    }
                }
            }

        }
        public void AddParent(PartiallySpecifiedState pss)        //returns true is a loop was detected
        {
            Parents.Add(pss);
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
                if (cf.Operator == "oneof")
                {
                    foreach (Formula f in cf.Operands)
                        AddHidden(f);
                }
                else if (cf.Operator != "and")
                    throw new NotImplementedException();
                else
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
            }
        }

        private string m_sToString = null;
        public override string ToString()
        {
            if (m_sToString == null)
            {
                foreach (Predicate p in Observed)
                {
                    if (p.Name == "at" && !p.Negation)
                    {
                        m_sToString = p.ToString();
                        break;
                    }
                }
                if (m_sToString == null)
                {
                    SortedSet<string> sObserved = new SortedSet<string>();
                    foreach (GroundedPredicate gpObserved in Observed)
                    {
                        if (!gpObserved.Negation && (!Problem.Domain.AlwaysKnown(gpObserved) || !Problem.Domain.AlwaysConstant(gpObserved)) && !gpObserved.Name.Contains("_Option_"))
                            sObserved.Add(gpObserved.ToString());
                    }
                    m_sToString = "";
                    foreach (string s in sObserved)
                        m_sToString += s + " ";
                }
            }
            return m_sToString;
        }


        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        //used to regress goal or precondition
        public bool RegressCondition(Formula f)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = f.Negate();
            while (pssCurrent != null)
            {
                Formula fReduced = fCurrent.Reduce(pssCurrent.Observed);
                if (fReduced.IsTrue(null))
                    return false;
                if (fReduced.IsFalse(null))
                    return true;
                if (pssCurrent.Predecessor != null)
                {
                    if (pssCurrent.GeneratingAction.HasConditionalEffects)
                    {
                        Formula fRegressed = fReduced.Regress(pssCurrent.GeneratingAction);
                        fCurrent = fRegressed;
                    }
                }
                pssCurrent = pssCurrent.Predecessor;

            }
            return !m_bsInitialBelief.ConsistentWith(fCurrent, false);
        }

        public bool IsGoalState()
        {
            m_bsInitialBelief.MaintainProblematicTag = true;
            Formula fReduced = Problem.Goal.Reduce(m_lObserved);
            if (fReduced.IsTrue(m_lObserved))
                return true;
            
            if (fReduced.IsFalse(m_lObserved))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, false))
            {
                return false;
            }
            return true;
        }

        public State WriteTaggedDomainAndProblem(out int cTags, out MemoryStream msModels)
        {
            return WriteTaggedDomainAndProblem(new List<Action>(), out cTags, out msModels);
        }

        public State WriteTaggedDomainAndProblemDeadEnd(List<Formula> lMaybeDeadends, DeadendStrategies dsStrategy, bool bPreconditionFailure, out int cTags, out MemoryStream msModels)
        {
            return WriteTaggedDomainAndProblemDeadEnd(new List<Action>(), lMaybeDeadends, dsStrategy, bPreconditionFailure, out cTags, out msModels);
        }

        public State WriteTaggedDomainAndProblem(CompoundFormula cfGoal, out int cTags, out MemoryStream msModels)
        {
            return WriteTaggedDomainAndProblem(cfGoal, new List<Action>(), out cTags, out msModels);
        }

        private State GetCurrentState(List<Predicate> lPredicates)
        {
            State s = new State(Problem);
            
            foreach (Predicate p in Observed)
                s.AddPredicate(p);
            return s;
        }

        private State WriteTaggedDomainAndProblem(List<Action> lActions, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.m_sPredecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblem(this, lActions, out cTags, out msModels);
        }

        private State WriteTaggedDomainAndProblemDeadEnd(List<Action> lActions, List<Formula> lMaybeDeadends, DeadendStrategies dsStrategy, bool bPreconditionFailure, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.m_sPredecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblemDeadEnd(this, lActions, lMaybeDeadends, dsStrategy, bPreconditionFailure, out cTags, out msModels);
        }


        private State WriteTaggedDomainAndProblem(CompoundFormula cfGoal, List<Action> lActions, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.m_sPredecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblem(cfGoal, lActions, out cTags, out msModels);
        }

        public PartiallySpecifiedState Predecessor { get { return m_sPredecessor; } }

        private PartiallySpecifiedState m_pssFirstChild;
        private ConditionalPlanTreeNode m_nPlan;
        public ConditionalPlanTreeNode Plan
        {
            set
            {
                m_nPlan = value;
                // if (value.ID == 50)
                //  Debug.WriteLine("dd");
            }
            get
            {
                return m_nPlan;
            }
        }

        static TimeSpan tsInUpdateClosed = new TimeSpan();

        public void UpdateClosedStates(List<PartiallySpecifiedState> lClosedStates, Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisited, Domain d, HashSet<Predicate> hsDeadEndList = null)
        {
            /***********************************************************************************
            StreamWriter swClosed = new StreamWriter("closed.txt", true);
            swClosed.WriteLine(ID);
            swClosed.Close();
            /**********************************************************************************/

            DateTime dtStart = DateTime.Now;

            //this can happen because of loops
            //if (ClosedState)
            //    return;

            //Debug.WriteLine("UpdateClosed " + ID + ", closed? " + ClosedState + ", " + ToString());

            //maybe already intialized due to an identical closed state
            if (m_lOfflinePredicatesKnown == null)
            {
                m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                m_lOfflinePredicatesUnknown = new HashSet<Predicate>();
                //m_dRequiredObservationsForReasoning = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            }

            //if (bAlreadyClosed)
            //    Debug.WriteLine("*");
            if (hsDeadEndList != null)
            {
                m_lOfflinePredicatesKnown = hsDeadEndList;
                Plan.DeadEnd = true;

            }
            else
            {
                if (IsGoalState())
                {
                    Plan.Goal = true;
                    m_lOfflinePredicatesKnown = Problem.Goal.GetAllPredicates();
                }
            }

            AddToClosedStates(lClosedStates, dVisited);

            foreach (PartiallySpecifiedState psParent in Parents)
            {
                UpdateClosedStates(psParent, lClosedStates, dVisited, d);
            }


        }

        static int c = 0;

        public void UpdateClosedStates(PartiallySpecifiedState psParent, List<PartiallySpecifiedState> lClosedStates,
                                        Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisited, Domain d)
        {

            //New meachanism for closed node identification:
            //1) When p is reasoned about:
            //1.a) in m_lOfflinePredicatesKnown and:
            //1.b) p is known at n
            //1.c) p is unknown at parent(n)
            //1.d) The observation between parent(n) and n is not over p
            //2) Add all the relevant vars for reasoning over p in parent(n).observed to m_lOfflinePredicatesKnown - this is an over approximation, perhaps only some of them are needed
            //3) Stop using the m_dRequiredObservationsForReasoning



            bool bChanged = false;

            //if (psParent.m_nPlan.ID == 95)
            //    Debug.Write("*");

            if (m_lOfflinePredicatesKnown == null)
            {
                bChanged = true;
                m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                m_lOfflinePredicatesUnknown = new HashSet<Predicate>();
            }

            Action a = null;
            if (psParent.m_nPlan.Action == null)
            {
                bChanged = true;
                a = GeneratingAction;
                if (a.Original != null)
                    a = GeneratingAction.Original;

                psParent.m_nPlan.Action = a;
            }
            else
                a = psParent.m_nPlan.Action;

            if (a.Observe == null)
                psParent.m_nPlan.SingleChild = m_nPlan;
            else
            {
                if (GeneratingObservation.GetAllPredicates().First().Negation)
                    psParent.m_nPlan.FalseObservationChild = m_nPlan;
                else
                    psParent.m_nPlan.TrueObservationChild = m_nPlan;
            }

            if (psParent.ChildCount == 1) //not the result of a sensing action
            {
                if (psParent.m_lOfflinePredicatesUnknown == null)
                {
                    bChanged = true;
                    psParent.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(m_lOfflinePredicatesUnknown);
                    psParent.m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                }
                HashSet<Predicate> lMandatoryEffects = a.GetMandatoryEffects();
                foreach (Predicate p in m_lOfflinePredicatesKnown)
                {
                    //if a predicate is always known and constant no need to do anything
                    if (!(d.AlwaysKnown(p) && d.AlwaysConstant(p)) && !lMandatoryEffects.Contains(p)/* && !(p.Name == "at")*/)
                    {
                        if (!psParent.m_lOfflinePredicatesKnown.Contains(p))
                        {
                            psParent.m_lOfflinePredicatesKnown.Add(p);
                            bChanged = true;
                        }
                    }
                }
                HashSet<Predicate> hsPreconditions = new HashSet<Predicate>();
                if (a.Preconditions != null)
                    hsPreconditions = a.Preconditions.GetAllPredicates();

                foreach (GroundedPredicate gp in hsPreconditions)
                {
                    //if a predicate is always known and constant no need to do anything
                    if (d.AlwaysKnown(gp) && d.AlwaysConstant(gp))
                        continue;

                    if (d.AlwaysConstant(gp) && !Problem.InitiallyUnknown(gp))
                        continue;


                    if (!psParent.m_lOfflinePredicatesKnown.Contains(gp))
                    {
                        psParent.m_lOfflinePredicatesKnown.Add(gp);
                        bChanged = true;
                    }
                }
            }
            else // sensing action - apply new algorithm
            {
                HashSet<Predicate> hsRelevantForReasoning = new HashSet<Predicate>();
                foreach (GroundedPredicate p in m_lOfflinePredicatesKnown)
                {
                    if (!p.Equals(GeneratingObservation))
                    {
                        if (psParent.Hidden.Contains(p.Canonical()))
                        {
                            //Debug.WriteLine("*");
                            foreach (Predicate pRelevantFor in Problem.GetRelevantPredicates(p))
                            {
                                if (psParent.Observed.Contains(pRelevantFor))
                                    hsRelevantForReasoning.Add(pRelevantFor);
                                if (psParent.Observed.Contains(pRelevantFor.Negate()))
                                    hsRelevantForReasoning.Add(pRelevantFor.Negate());
                            }
                        }
                    }
                }
                //if (hsRelevantForReasoning.Count > 0)
                //    Debug.Write("*");
                m_lOfflinePredicatesKnown.UnionWith(hsRelevantForReasoning);

                if (psParent.m_pssFirstChild == null)
                {
                    psParent.m_pssFirstChild = this;
                    bChanged = true;

                    return;
                }
                else
                {
                    //if (psParent.ID == 23)
                    //    Debug.Write("*");

                    HashSet<Predicate> hsDisagree = new HashSet<Predicate>();
                    foreach (Predicate p in psParent.m_pssFirstChild.Observed)
                        if (Observed.Contains(p.Negate()))
                            hsDisagree.Add(p);
                    foreach (Predicate p in Observed)
                        if (psParent.m_pssFirstChild.Observed.Contains(p.Negate()))
                            hsDisagree.Add(p);

                    if (psParent.m_lOfflinePredicatesUnknown == null)
                    {
                        psParent.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(psParent.m_pssFirstChild.m_lOfflinePredicatesUnknown);
                        bChanged = true;
                    }
                    psParent.m_lOfflinePredicatesUnknown.UnionWith(m_lOfflinePredicatesUnknown);
                    if (!psParent.m_lOfflinePredicatesUnknown.Add(((PredicateFormula)GeneratingObservation).Predicate.Canonical()))
                        bChanged = true;

                    if (psParent.m_lOfflinePredicatesKnown == null)
                        psParent.m_lOfflinePredicatesKnown = new HashSet<Predicate>();

                    HashSet<Predicate> hsAllRelevantPredicates = new HashSet<Predicate>(m_lOfflinePredicatesKnown);
                    hsAllRelevantPredicates.UnionWith(psParent.m_pssFirstChild.m_lOfflinePredicatesKnown);
                    if (a.Preconditions != null)
                    {
                        foreach (Predicate gp in a.Preconditions.GetAllPredicates())
                        {
                            if (d.AlwaysKnown(gp) && d.AlwaysConstant(gp))
                                continue;

                            if (d.AlwaysConstant(gp) && !Problem.InitiallyUnknown(gp))
                                continue;
                            hsAllRelevantPredicates.Add(gp);
                        }
                    }
                    //same action! only different observations!
                    //if (psParent.m_pssFirstChild.GeneratingAction.Preconditions != null)
                    //    hsAllRelevantPredicates.UnionWith(psParent.m_pssFirstChild.GeneratingAction.Preconditions.GetAllPredicates());

                    foreach (Predicate p in hsAllRelevantPredicates)
                    {
                        if (hsDisagree.Contains(p))
                            psParent.m_lOfflinePredicatesUnknown.Add(p.Canonical());
                        else if (!psParent.m_lOfflinePredicatesUnknown.Contains(p.Canonical()))
                        {
                            psParent.m_lOfflinePredicatesKnown.Add(p);
                            bChanged = true;
                        }
                    }


                    psParent.m_pssFirstChild.AddToClosedStates(lClosedStates, dVisited);

                    //Debug.WriteLine("Finished state:" + pssIter + "\n" + psParent.m_nPlan.ToString());
                }
            }
            if (bChanged)
                psParent.UpdateClosedStates(lClosedStates, dVisited, d);


        }


        public void UpdateClosedStates_m_dRequiredObservationsForReasoning(PartiallySpecifiedState psParent, List<PartiallySpecifiedState> lClosedStates,
            Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisited, Domain d)
        {



            bool bChanged = false;
            //if (psParent.ClosedState)
            //   return;
            /*
            bool b94 = false;
            foreach (string s in m_lHistory)
                if (s.StartsWith("84)"))
                    b94 = true;
            if (b94)
                Debug.Write("*");
                */
            //maybe already intialized due to an identical closed state


            if (psParent.m_nPlan.ID == 95)
                Debug.Write("*");

            if (m_lOfflinePredicatesKnown == null)
            {
                bChanged = true;
                m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                m_lOfflinePredicatesUnknown = new HashSet<Predicate>();
                //m_dRequiredObservationsForReasoning = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            }

            Action a = null;
            if (psParent.m_nPlan.Action == null)
            {
                bChanged = true;
                a = GeneratingAction;
                if (a.Original != null)
                    a = GeneratingAction.Original;

                psParent.m_nPlan.Action = a;
            }
            else
                a = psParent.m_nPlan.Action;

            //if (psParent.ID == 190)
            //    Debug.WriteLine("ss");
            if (a.Observe == null)
                psParent.m_nPlan.SingleChild = m_nPlan;
            else
            {
                if (GeneratingObservation.GetAllPredicates().First().Negation)
                    psParent.m_nPlan.FalseObservationChild = m_nPlan;
                else
                    psParent.m_nPlan.TrueObservationChild = m_nPlan;
            }

            if (psParent.ChildCount == 1)
            {
                if (psParent.m_lOfflinePredicatesUnknown == null)
                {
                    bChanged = true;
                    psParent.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(m_lOfflinePredicatesUnknown);
                    psParent.m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                }
                HashSet<Predicate> lMandatoryEffects = a.GetMandatoryEffects();
                foreach (Predicate p in m_lOfflinePredicatesKnown)
                {
                    //if a predicate is always known and constant no need to do anything
                    if (!(d.AlwaysKnown(p) && d.AlwaysConstant(p)) && !lMandatoryEffects.Contains(p) && !(p.Name == "at"))
                    {
                        if (!psParent.m_lOfflinePredicatesKnown.Contains(p))
                        {
                            psParent.m_lOfflinePredicatesKnown.Add(p);
                            bChanged = true;
                        }
                    }
                }
                HashSet<Predicate> hsPreconditions = new HashSet<Predicate>();
                if (a.Preconditions != null)
                    hsPreconditions = a.Preconditions.GetAllPredicates();

                if (psParent.m_dRequiredObservationsForReasoning == null)
                    psParent.m_dRequiredObservationsForReasoning = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>(m_dRequiredObservationsForReasoning);




                foreach (GroundedPredicate gp in hsPreconditions)
                {
                    //if a predicate is always known and constant no need to do anything
                    if (d.AlwaysKnown(gp) && d.AlwaysConstant(gp))
                        continue;

                    if (d.AlwaysConstant(gp) && !Problem.InitiallyUnknown(gp))
                        continue;

                    if (Problem.InitiallyUnknown(gp) && !m_lDirectlyObserved.Contains(gp))
                    {
                        if (!psParent.m_dRequiredObservationsForReasoning.ContainsKey(gp))
                        {
                            psParent.m_dRequiredObservationsForReasoning[gp] = new List<HashSet<GroundedPredicate>>();
                            psParent.m_dRequiredObservationsForReasoning[gp].Add(new HashSet<GroundedPredicate>());
                            bChanged = true;
                        }
                    }

                    if (!psParent.m_lOfflinePredicatesKnown.Contains(gp))
                    {
                        psParent.m_lOfflinePredicatesKnown.Add(gp);
                        bChanged = true;
                    }
                }


            }

            else if (psParent.m_pssFirstChild == null)
            {
                psParent.m_pssFirstChild = this;
                bChanged = true;
                //if (!bAlreadyClosed)
                //    pssIter.AddToClosedStates(dClosedStates);

                return;
            }
            else
            {
                if (psParent.ID == 23)
                    Debug.Write("*");

                HashSet<Predicate> hsDisagree = new HashSet<Predicate>();
                foreach (Predicate p in psParent.m_pssFirstChild.Observed)
                    if (Observed.Contains(p.Negate()))
                        hsDisagree.Add(p);
                foreach (Predicate p in Observed)
                    if (psParent.m_pssFirstChild.Observed.Contains(p.Negate()))
                        hsDisagree.Add(p);

                if (psParent.m_lOfflinePredicatesUnknown == null)
                {
                    psParent.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(psParent.m_pssFirstChild.m_lOfflinePredicatesUnknown);
                    bChanged = true;
                }
                psParent.m_lOfflinePredicatesUnknown.UnionWith(m_lOfflinePredicatesUnknown);
                if (!psParent.m_lOfflinePredicatesUnknown.Add(((PredicateFormula)GeneratingObservation).Predicate.Canonical()))
                    bChanged = true;

                if (psParent.m_lOfflinePredicatesKnown == null)
                    psParent.m_lOfflinePredicatesKnown = new HashSet<Predicate>();

                HashSet<Predicate> hsAllRelevantPredicates = new HashSet<Predicate>(m_lOfflinePredicatesKnown);
                hsAllRelevantPredicates.UnionWith(psParent.m_pssFirstChild.m_lOfflinePredicatesKnown);
                if (a.Preconditions != null)
                {
                    foreach (Predicate gp in a.Preconditions.GetAllPredicates())
                    {
                        if (d.AlwaysKnown(gp) && d.AlwaysConstant(gp))
                            continue;

                        if (d.AlwaysConstant(gp) && !Problem.InitiallyUnknown(gp))
                            continue;
                        hsAllRelevantPredicates.Add(gp);
                    }
                }
                //same action! only different observations!
                //if (psParent.m_pssFirstChild.GeneratingAction.Preconditions != null)
                //    hsAllRelevantPredicates.UnionWith(psParent.m_pssFirstChild.GeneratingAction.Preconditions.GetAllPredicates());

                foreach (Predicate p in hsAllRelevantPredicates)
                {
                    if (hsDisagree.Contains(p))
                        psParent.m_lOfflinePredicatesUnknown.Add(p.Canonical());
                    else if (!psParent.m_lOfflinePredicatesUnknown.Contains(p.Canonical()))
                    {
                        psParent.m_lOfflinePredicatesKnown.Add(p);
                        bChanged = true;
                    }
                }



                if (psParent.AddRelevantVariables(m_dRequiredObservationsForReasoning, ((PredicateFormula)GeneratingObservation).Predicate))
                    bChanged = true;
                if (psParent.AddRelevantVariables(psParent.m_pssFirstChild.m_dRequiredObservationsForReasoning, ((PredicateFormula)psParent.m_pssFirstChild.GeneratingObservation).Predicate))
                    bChanged = true;


                psParent.m_pssFirstChild.AddToClosedStates(lClosedStates, dVisited);

                //Debug.WriteLine("Finished state:" + pssIter + "\n" + psParent.m_nPlan.ToString());
            }
            if (bChanged)
                psParent.UpdateClosedStates(lClosedStates, dVisited, d);


        }


        public static int ClosedStates = 0;
        public static int RelevantCount = 0;

        private void FilterRequiredObservationsForReasoning()
        {
            Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>> dFilteredRelevantVariables = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            foreach (GroundedPredicate gpReasoned in m_dRequiredObservationsForReasoning.Keys)
            {
                bool bRelevantVariablesObserved = false;
                HashSet<GroundedPredicate> lRelevant = Problem.GetRelevantPredicates(gpReasoned);
                foreach (GroundedPredicate p in lRelevant)
                {
                    if (m_lDirectlyObserved.Contains(p) || m_lDirectlyObserved.Contains(p.Negate()))
                    {
                        bRelevantVariablesObserved = true;
                        break;

                    }
                }

                if (bRelevantVariablesObserved)
                {
                    dFilteredRelevantVariables[gpReasoned] = new List<HashSet<GroundedPredicate>>();
                    foreach (HashSet<GroundedPredicate> hs in m_dRequiredObservationsForReasoning[gpReasoned])
                    {
                        bool bContains = false;
                        foreach (HashSet<GroundedPredicate> hsExists in dFilteredRelevantVariables[gpReasoned])
                        {
                            if (hs.Count == hsExists.Count)
                            {
                                bool bDifferent = false;
                                foreach (GroundedPredicate gpPredicate in hs)
                                {
                                    if (!hsExists.Contains(gpPredicate))
                                    {
                                        bDifferent = true;
                                        break;
                                    }
                                }
                                if (!bDifferent)
                                {
                                    bContains = true;
                                    break;
                                }
                            }
                        }
                        if (!bContains)
                            dFilteredRelevantVariables[gpReasoned].Add(hs);
                    }
                }
            }

            m_dRequiredObservationsForReasoning = dFilteredRelevantVariables;

        }

        private bool AddToClosedStates(List<PartiallySpecifiedState> lClosedStates, Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dVisited)
        {

            ClosedStates++;
            lClosedStates.Add(this);

            if (m_dRequiredObservationsForReasoning != null)
                FilterRequiredObservationsForReasoning();

            dVisited.Remove(this);
            /*
            m_lObserved = null;
            m_lHidden = null;
            m_bsInitialBelief = null;
            */
            ClosedState = true;

            return true;
        }

        private bool AddRelevantVariables(Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>> dRelevant, Predicate pObservation)
        {
            bool bChanged = false;
            GroundedPredicate gpObservation = (GroundedPredicate)pObservation;
            if (m_dRequiredObservationsForReasoning == null)
            {
                bChanged = true;
                m_dRequiredObservationsForReasoning = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            }
            foreach (GroundedPredicate pReasoned in dRelevant.Keys)
            {
                if (!m_dRequiredObservationsForReasoning.ContainsKey(pReasoned))
                {
                    bChanged = true;
                    m_dRequiredObservationsForReasoning[pReasoned] = new List<HashSet<GroundedPredicate>>();
                }
                bool bRelevant = Problem.IsRelevantFor(gpObservation, pReasoned);
                foreach (HashSet<GroundedPredicate> hs in dRelevant[pReasoned])
                {
                    HashSet<GroundedPredicate> hsNew = new HashSet<GroundedPredicate>(hs);
                    if (bRelevant)
                        hsNew.Add(gpObservation);
                    m_dRequiredObservationsForReasoning[pReasoned].Add(hsNew);
                }
            }
            return bChanged;
        }

        public bool ConsistentWith(Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>> dRelevantForOther)
        {
            foreach (KeyValuePair<GroundedPredicate, List<HashSet<GroundedPredicate>>> p in dRelevantForOther)
            {
                foreach (HashSet<GroundedPredicate> hs in p.Value)
                {
                    if (p.Value.Count > 0 && !ConsistentWith(hs, p.Key))
                        return false;
                }
            }
            return true;
        }

        private bool ConsistentWith(HashSet<GroundedPredicate> hsObservations, GroundedPredicate gpReasoned)
        {
            if (Observed.Contains(gpReasoned))
                return true;
            if (!Hidden.Contains(gpReasoned.Canonical()))
                if (Observed.Contains(gpReasoned.Negate()))
                    return false;

            HashSet<Predicate> hsLearned = new HashSet<Predicate>();
            foreach (Predicate pObserved in hsObservations)
                hsLearned.Add(pObserved);



            List<Formula> lHidden = new List<Formula>(m_bsInitialBelief.Hidden);
            foreach (Predicate p in hsLearned)
                lHidden.Add(new PredicateFormula(p));

            HashSet<Predicate> lAssignment = new HashSet<Predicate>();
            bool bValid = m_bsInitialBelief.ApplyUnitPropogation(lHidden, lAssignment);

            bool bLearned = lAssignment.Contains(gpReasoned);
            return bLearned;
        }


        public HashSet<Predicate> GetRelevantVariables(HashSet<Predicate> hsUnknown)
        {
            HashSet<Predicate> hsRelevant = new HashSet<Predicate>();
            List<CompoundFormula> lHidden = new List<CompoundFormula>(m_bsInitialBelief.Hidden);
            for (int i = 0; i < lHidden.Count; i++)
            {
                CompoundFormula cf = lHidden[i];
                if (cf != null)
                {
                    HashSet<Predicate> hsPredicates = cf.GetAllPredicates();
                    foreach (Predicate p in hsPredicates)
                    {
                        if (!Problem.Domain.Observable(p))
                        {
                            if (hsUnknown.Contains(p.Canonical()))
                            {
                                foreach (Predicate pAdd in hsPredicates)
                                {
                                    hsRelevant.Add(pAdd.Canonical());

                                }
                                lHidden[i] = null;
                            }
                        }
                    }
                }
            }
            return hsRelevant;
        }



        private void CopyClosedState(PartiallySpecifiedState pssClosed)
        {
            Plan = pssClosed.Plan;

            //if (Plan.ID == 95)
            //    Debug.Write("*");

            m_lOfflinePredicatesUnknown = pssClosed.m_lOfflinePredicatesUnknown;
            m_lOfflinePredicatesKnown = pssClosed.m_lOfflinePredicatesKnown;

            if (pssClosed.m_dRequiredObservationsForReasoning != null)
            {
                m_dRequiredObservationsForReasoning = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
                foreach (GroundedPredicate gpReasoned in pssClosed.m_dRequiredObservationsForReasoning.Keys)
                {
                    if (!m_lDirectlyObserved.Contains(gpReasoned))
                    {
                        m_dRequiredObservationsForReasoning[gpReasoned] = pssClosed.m_dRequiredObservationsForReasoning[gpReasoned];
                    }
                }
            }
        }

        public static int amount_of_offline_pruned_states = 0;
        TimeSpan tsInIsClosed = new TimeSpan();
        public bool IsClosedState(List<PartiallySpecifiedState> lClosedStates)
        {
            if (!Problem.Domain.IsSimple)
                return IsGoalState();

            DateTime dtStart = DateTime.Now;

            foreach (PartiallySpecifiedState pssClosed in lClosedStates)
            {
                bool bKnownContained = pssClosed.m_lOfflinePredicatesKnown == null ||
                    pssClosed.m_lOfflinePredicatesKnown.Count == 0 ||
                    pssClosed.m_lOfflinePredicatesKnown.IsSubsetOf(Observed);
                if (bKnownContained && pssClosed.m_lOfflinePredicatesUnknown.Count == 0)
                {

                    //  if (pssClosed.ID == 50)
                    //     Debug.WriteLine("d");
                    CopyClosedState(pssClosed);
                    //if (!SDRPlanner.CheckPlan(Clone(), pssClosed.m_nPlan, new List<string>()))
                    //   Debug.Write("*");
                    return true;
                }
                if (!bKnownContained)
                    continue;

                bool bUnknownContained = pssClosed.m_lOfflinePredicatesUnknown == null ||
                    pssClosed.m_lOfflinePredicatesUnknown.Count == 0 ||
                    pssClosed.m_lOfflinePredicatesUnknown.IsSubsetOf(Hidden);

                if (bKnownContained && bUnknownContained)
                {
                    bool bConsistentWith = true;
                    if (pssClosed.m_dRequiredObservationsForReasoning != null)
                        bConsistentWith = ConsistentWith(pssClosed.m_dRequiredObservationsForReasoning);

                    if (bConsistentWith)
                    {


                        amount_of_offline_pruned_states++;
                        CopyClosedState(pssClosed);

                        tsInIsClosed += DateTime.Now - dtStart;

                        return true;
                    }

                }
            }

            tsInIsClosed += DateTime.Now - dtStart;
            return false;
        }

        public PartiallySpecifiedState FindSimilarState(Dictionary<string, List<PartiallySpecifiedState>> dClosedStates)
        {
            if (!Problem.Domain.IsSimple)
                return null;

            int cMaxIdenticalUnknown = 2;
            List<PartiallySpecifiedState> lSimilar = new List<PartiallySpecifiedState>();
            foreach (List<PartiallySpecifiedState> dc in dClosedStates.Values)
            {
                foreach (PartiallySpecifiedState pssClosed in dc)
                {
                    bool bKnownContained = pssClosed.m_lOfflinePredicatesKnown.Count == 0 || pssClosed.m_lOfflinePredicatesKnown.IsSubsetOf(Observed);
                    if (bKnownContained)
                        continue;//because we don't want the exact same - otherwise IsClosed would have identify it
                    /* probably will never happen
                    if (m_lHidden.SetEquals(pssClosed.m_lHidden))
                    {

                        bool bEqualObserved = true;

                        foreach (GroundedPredicate gp in pssClosed.m_lObserved)
                        {
                            if (Problem.InitiallyUnknown(gp))
                            {
                                if (!m_lObserved.Contains(gp))
                                {
                                    bEqualObserved = false;
                                    break;
                                }
                            }
                        }

                        if (bEqualObserved)
                            Debug.Write("*");
                    }
                    */
                    bool bUnknownContained = pssClosed.m_lOfflinePredicatesUnknown.Count == 0 || pssClosed.m_lOfflinePredicatesUnknown.IsSubsetOf(Hidden);
                    if (!bUnknownContained)
                        continue;
                    bool bHiddenKnownContained = true;

                    int cIdenticalKnown = 0;

                    foreach (GroundedPredicate gp in pssClosed.m_lOfflinePredicatesKnown)
                    {
                        if (Problem.InitiallyUnknown(gp))
                        {
                            if (Hidden.Contains(gp.Canonical()) || Observed.Contains(gp.Negate()))
                                bHiddenKnownContained = false;
                            else
                                cIdenticalKnown++;
                        }
                    }
                    if (!bHiddenKnownContained)
                        continue;

                    if (bHiddenKnownContained && bUnknownContained)
                    {
                        if (cIdenticalKnown > cMaxIdenticalUnknown)
                        {
                            cMaxIdenticalUnknown = cIdenticalKnown;
                            lSimilar = new List<PartiallySpecifiedState>();
                        }
                        else if (cIdenticalKnown == cMaxIdenticalUnknown)
                            lSimilar.Add(pssClosed);
                    }
                }
            }
            if (lSimilar.Count == 0)
                return null;
            return lSimilar.First();
        }

        public Formula regress(Formula f, int steps)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = f;

            Formula fReduced = null;
            int cRegressions = 0;
            List<PartiallySpecifiedState> lFuture = new List<PartiallySpecifiedState>();
            while (pssCurrent.m_sPredecessor != null && steps > 0)
            {
                lFuture.Add(pssCurrent);
                steps--;
                fReduced = fCurrent.Reduce(pssCurrent.Observed);
                if (fReduced.IsTrue(null))
                    return new PredicateFormula(new GroundedPredicate("True"));
                if (fReduced.IsFalse(null))
                    return new PredicateFormula(new GroundedPredicate("False"));

                Formula fToRegress = fReduced;
                if (fToRegress is CompoundFormula)
                {
                    //bool bChanged = false;
                    //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
                }
                if (fToRegress.IsTrue(pssCurrent.Observed))
                    return new PredicateFormula(new GroundedPredicate("True"));
                if (fToRegress.IsFalse(pssCurrent.Observed))
                    return new PredicateFormula(new GroundedPredicate("False"));
                Formula fRegressed = fToRegress.Regress(pssCurrent.GeneratingAction, pssCurrent.Observed);
                //Formula fRegressed = fToRegress.Regress(GeneratingAction);
                cRegressions++;

                fCurrent = fRegressed;
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            fReduced = fCurrent.Reduce(pssCurrent.Observed);
            return fReduced;
        }


    }
}

