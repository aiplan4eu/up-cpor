using CPORLib.Algorithms;
using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.Tools;
using Microsoft.SolverFoundation.Services;
using Microsoft.SolverFoundation.Solvers;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using static CPORLib.Tools.Options;
using Action = CPORLib.PlanningModel.PlanningAction;


namespace CPORLib.PlanningModel
{
    public class BeliefState
    {
        public ISet<Predicate> Observed { get { return m_lObserved; } }
        public List<CompoundFormula> Hidden { get { return m_lHiddenFormulas; } }
        public HashSet<Predicate> Unknown { get; private set; }
        private List<CompoundFormula> m_lHiddenFormulas;
        private List<CompoundFormula> m_lOriginalHiddenFormulas;
        private Dictionary<GroundedPredicate, List<int>> m_dMapPredicatesToFormulas;

        private List<EfficientFormula> m_lEfficientHidden;
        private Dictionary<GroundedPredicate, int> m_dMapPredicatesToIndexes;
        private List<GroundedPredicate> m_dMapIndexToPredicate;
        private List<List<int>> m_dMapPredicateToEfficientFormula;

        private CompoundFormula m_cfCNFHiddenState;
        //protected List<Predicate> m_lObserved;
        protected HashSet<Predicate> m_lObserved;
        public List<Action> AvailableActions { get; protected set; }
        private BeliefState m_sPredecessor;
        public Problem Problem { get; private set; }
        public State UnderlyingEnvironmentState { get; set; }
        private List<ISet<Predicate>> m_lCurrentTags;
        private ISet<Predicate> m_lProblematicTag;
        private List<ISet<Predicate>> m_lDeadendTags;
        public bool MaintainProblematicTag { get; set; }
        public string OutputType { get { return "SAS"; } }

        public static int bsCOUNT = 0;
        public int ID;

        public static bool UseEfficientFormulas = false;

        private int m_cNonDetChoices;

        public Dictionary<string, double> FunctionValues { get; private set; }

        public BeliefState(Problem p)
        {
            Problem = p;
            m_sPredecessor = null;
            m_lObserved = new HashSet<Predicate>();
            Unknown = new HashSet<Predicate>();
            m_lHiddenFormulas = new List<CompoundFormula>();
            m_lOriginalHiddenFormulas = new List<CompoundFormula>();
            m_dMapPredicatesToFormulas = new Dictionary<GroundedPredicate, List<int>>();

            m_lEfficientHidden = new List<EfficientFormula>();
            m_dMapPredicatesToIndexes = new Dictionary<GroundedPredicate, int>();
            m_dMapIndexToPredicate = new List<GroundedPredicate>();
            m_dMapPredicateToEfficientFormula = new List<List<int>>();

            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = null;
            m_cfCNFHiddenState = new CompoundFormula("and");
            FunctionValues = new Dictionary<string, double>();
            foreach (string sFunction in Problem.Domain.Functions)
            {
                FunctionValues[sFunction] = 0.0;
            }

            m_lDeadendTags = new List<ISet<Predicate>>();

            bsCOUNT++;
            ID = bsCOUNT;
            m_cNonDetChoices = 0;
        }
        public BeliefState(BeliefState sToCopy)
            : this(sToCopy.Problem)
        {
            m_lHiddenFormulas = new List<CompoundFormula>(sToCopy.Hidden);
            m_lOriginalHiddenFormulas = new List<CompoundFormula>(sToCopy.m_lOriginalHiddenFormulas);
            m_dMapPredicatesToFormulas = new Dictionary<GroundedPredicate, List<int>>();
            foreach (KeyValuePair<GroundedPredicate, List<int>> pair in sToCopy.m_dMapPredicatesToFormulas)
            {
                m_dMapPredicatesToFormulas[pair.Key] = new List<int>();
                foreach (int i in pair.Value)
                {
                    m_dMapPredicatesToFormulas[pair.Key].Add(i);
                }
            }
            m_dMapPredicatesToIndexes = new Dictionary<GroundedPredicate, int>(sToCopy.m_dMapPredicatesToIndexes);
            m_dMapPredicateToEfficientFormula = new List<List<int>>();
            foreach (List<int> list in sToCopy.m_dMapPredicateToEfficientFormula)
            {
                List<int> newList = new List<int>();
                foreach (int i in list)
                {
                    newList.Add(i);
                }
                m_dMapPredicateToEfficientFormula.Add(newList);
            }
            m_lObserved = new HashSet<Predicate>(sToCopy.Observed);
            Unknown = new HashSet<Predicate>(sToCopy.Unknown);
            m_cfCNFHiddenState = sToCopy.m_cfCNFHiddenState;

            if (sToCopy.m_lDeadendTags != null)
                m_lDeadendTags = new List<ISet<Predicate>>(sToCopy.m_lDeadendTags);
            if (sToCopy.m_lCurrentTags != null)
                m_lCurrentTags = new List<ISet<Predicate>>(sToCopy.m_lCurrentTags);


            

            bsCOUNT++;
            ID = bsCOUNT;
            m_cNonDetChoices = sToCopy.m_cNonDetChoices;
        }

        public bool ConsistentWith(Predicate p, bool bConsiderHiddenState)
        {
            foreach (Predicate pState in Observed)
            {
                if (!p.ConsistentWith(pState))
                    return false;
            }
            if (bConsiderHiddenState)
            {
                //need to also check whether p is consistent with the hidden state
                /*
                List<CompoundFormula> lReducedHidden = new List<CompoundFormula>();
                List<Predicate> lKnown = new List<Predicate>(Observed);
                lKnown.Add(p);
                foreach (CompoundFormula cfHidden in m_lHidden)
                {
                    Formula cfReduced = cfHidden.Reduce(lKnown);
                    if (cfReduced.IsFalse(lKnown))
                        return false;
                    if (cfReduced is PredicateFormula)
                    {
                        Predicate pReduced = ((PredicateFormula)cfReduced).Predicate;
                        lKnown.Add(pReduced);
                    }
                    else
                        lReducedHidden.Add((CompoundFormula)cfReduced);
                }
                if (RunSatSolver(lReducedHidden, 1).Count == 0)
                    return false;
                 * */
                CompoundFormula cfCNF = (CompoundFormula)m_cfCNFHiddenState.Clone();
                cfCNF.AddOperand(p);
                throw new NotImplementedException();
                List<List<Predicate>> lConsistentAssignments = null;// RunSatSolver(cfCNF, 1);
                if (lConsistentAssignments.Count == 0)
                {
                    return false;
                }
            }
            return true;
        }

        public bool ConsistentWith(State s)
        {
            foreach (Predicate pState in s.Predicates)
            {
                if (!ConsistentWith(pState, false))
                    return false;
            }
            return true;
        }

        public bool ConsistentWith(Formula fOriginal, bool bCheckingActionPreconditions)
        {

            Formula f = fOriginal.Reduce(Observed);
            if (f.IsFalse(Observed))
                return false;
            if (f.IsTrue(Observed))
                return true;

            bool bValid = true;

            CompoundFormula cf = null;
            List<PredicateFormula> lPredicates = new List<PredicateFormula>();
            List<CompoundFormula> lFormulas = new List<CompoundFormula>();
            if (f is PredicateFormula)
            {
                lPredicates.Add((PredicateFormula)f);
            }
            else
            {
                cf = (CompoundFormula)f;
                CompoundFormula cfCNF = (CompoundFormula)cf.ToCNF();
                if (cfCNF.Operator == "and")
                {
                    foreach (Formula fSub in cfCNF.Operands)
                    {
                        if (fSub is PredicateFormula)
                            lPredicates.Add((PredicateFormula)fSub);
                        else
                            lFormulas.Add((CompoundFormula)fSub);
                    }
                }
                else
                    lFormulas.Add(cfCNF);

            }

            //if we got a grounded predicate, whose value is not unknown, and its value is false, then it is inconsistent with the current state
            if(lPredicates.Count > 0)
            {
                foreach (PredicateFormula pf in lPredicates)
                {
                    GroundedPredicate gp = (GroundedPredicate)pf.Predicate;
                    bool bKnown = true;
                    if (m_dMapPredicatesToFormulas.ContainsKey((GroundedPredicate)gp.Canonical()))
                    {
                        foreach (int idx in m_dMapPredicatesToFormulas[(GroundedPredicate)gp.Canonical()])
                        {
                            if (m_lHiddenFormulas[idx] != null)
                            {
                                bKnown = false;
                                break;
                            }
                        }
                    }
                    if(bKnown)
                    {
                        if(!m_lObserved.Contains(gp) && !gp.Negation)
                        {
                            return false;
                        }
                    }
                }
            }

            if (lFormulas.Count == 0)
            {
                HashSet<Predicate> lAssignment = new HashSet<Predicate>();
                List<Formula> lHidden = new List<Formula>();
                foreach(Formula fHidden in m_lHiddenFormulas)
                    //if(fHidden != null)
                        lHidden.Add(fHidden);
                foreach (PredicateFormula pf in lPredicates)
                {
                    lHidden.Add(pf);
                }
                bValid = ApplyUnitPropogation(lHidden, lAssignment);
                if (bValid && MaintainProblematicTag && bCheckingActionPreconditions)
                {
                    m_lProblematicTag = new HashSet<Predicate>();
                    foreach (Predicate p in lAssignment)
                        m_lProblematicTag.Add(p);
                }

            }
            else
            {
                if (lPredicates.Count > 0)
                {
                    HashSet<int> lIndexes = new HashSet<int>();
                    HashSet<Predicate> lKnown = new HashSet<Predicate>();
                    foreach (PredicateFormula pf in lPredicates)
                    {
                        if (m_dMapPredicatesToFormulas.ContainsKey((GroundedPredicate)pf.Predicate.Canonical()))
                        {
                            lKnown.Add(pf.Predicate);
                            foreach (int idx in m_dMapPredicatesToFormulas[(GroundedPredicate)pf.Predicate.Canonical()])
                                lIndexes.Add(idx);
                        }
                    }
                    foreach (int idx in lIndexes)
                    {
                        if (m_lHiddenFormulas[idx] != null && m_lHiddenFormulas[idx].IsFalse(lKnown))
                            bValid = false;
                    }
                }

                if(bValid)
                {
                    if (lFormulas.Count > 0)
                    {
                        List<Formula> lHidden = new List<Formula>(m_lHiddenFormulas);
                        lHidden.AddRange(lFormulas);
                        lHidden.AddRange(lPredicates);
                        List<ISet<Predicate>> lConsistentAssignments = RunSatSolver(lHidden, 1);
                        bValid = lConsistentAssignments.Count > 0;
                        if (MaintainProblematicTag && bCheckingActionPreconditions)
                            m_lProblematicTag = null;
                        if (bValid)
                        {
                            if (MaintainProblematicTag && bCheckingActionPreconditions)
                            {
                                m_lProblematicTag = lConsistentAssignments[0];
                            }
                        }
                        else
                        {
                            //we have just discovered something that is inconsistent with the initial belief, so we can add its negation to the initial belief
                            AddReasoningFormula(f.Negate(), new HashSet<int>());
                        }
                        //MaintainProblematicTag = false;

                    }
                }
            }
            if (false)//for debugging the ongoing reduction of hidden formulas given observations - here I use the original formulas + the observed
            {
                List<Formula> lHidden = new List<Formula>(m_lOriginalHiddenFormulas);
                foreach (GroundedPredicate gp in Observed)
                    lHidden.Add(new PredicateFormula(gp));
                lHidden.AddRange(lPredicates);
                List<ISet<Predicate>> lConsistentAssignments = RunSatSolver(lHidden, 1);
                bValid = lConsistentAssignments.Count > 0;
                if (MaintainProblematicTag)
                    m_lProblematicTag = null;
                if (bValid)
                {
                    if (MaintainProblematicTag && bCheckingActionPreconditions)
                    {
                        m_lProblematicTag = lConsistentAssignments[0];
                        /*
                        foreach (CompoundFormula cfHidden in m_lOriginalHiddenFormulas)
                        {
                            if (cfHidden.ToString().Contains("obs1-at p2_1"))
                                    Debug.WriteLine("*");
                            Formula fReduced = cfHidden.Reduce(m_lProblematicTag);
                            if (fReduced is PredicateFormula)
                            {
                                PredicateFormula pf = (PredicateFormula)fReduced;
                                if (pf.Predicate.Name == "P_FALSE")
                                    Debug.WriteLine("*");
                                else if (pf.Predicate.Name != "P_TRUE" && !pf.Predicate.Negation)
                                    Debug.WriteLine(pf);
                                 
                            }
                        }
                         * */
                    }
                }
                //MaintainProblematicTag = false;
                //return lConsistentAssignments.Count > 0;
            }

            if (MaintainProblematicTag && bCheckingActionPreconditions && bValid)
            {
                //filter the problematic tag
                ISet<Predicate> lFiltered = new HashSet<Predicate>();
                Formula fCurrent = fOriginal, fReduced = null;
                foreach (Predicate p in m_lProblematicTag)
                {
                    HashSet<Predicate> lAssignment = new HashSet<Predicate>();
                    lAssignment.Add(p);
                    fReduced = fCurrent.Reduce(lAssignment);
                    if (!fReduced.Equals(fCurrent))
                        lFiltered.Add(p);
                    if (fReduced.IsTrue(null))
                    {
                        break;
                    }
                    fCurrent = fReduced;
                }
                m_lProblematicTag = lFiltered;
                MaintainProblematicTag = false;
            }
            return bValid;
        }
        public bool AddObserved(Predicate p)
        {
            bool bNew = false;
            if (p == Utilities.TRUE_PREDICATE)
                return false;
            Debug.Assert(p != Utilities.FALSE_PREDICATE, "Adding P_FALSE");

#if DEBUG
            if (UnderlyingEnvironmentState != null &&
                ((p.Negation == false && !UnderlyingEnvironmentState.Contains(p)) ||
                (p.Negation == true && UnderlyingEnvironmentState.Contains(p.Negate()))))
                Debug.WriteLine("Adding a predicate that doesn't exist");
#endif 

            Unknown.Remove(p.Canonical());
            if (!m_lObserved.Contains(p))
            {
                Predicate pNegate = p.Negate();
                if (m_lObserved.Contains(pNegate))
                    m_lObserved.Remove(pNegate);
                bNew = true;
            }
            m_lObserved.Add(p);
            return bNew;
        }
        public void AddObserved(Formula f)
        {
            if (f is PredicateFormula)
                AddObserved(((PredicateFormula)f).Predicate);
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operator == "and")
                    foreach (Formula fSub in cf.Operands)
                        AddObserved(fSub);
                else
                    throw new NotImplementedException();
            }
        }

        public void ToSimpleForm()
        {
            List<CompoundFormula> lHidden = new List<CompoundFormula>();
            foreach (CompoundFormula cfHidden in m_lHiddenFormulas)
            {
                lHidden.Add(cfHidden.ToSimpleForm());
            }
            m_lHiddenFormulas = lHidden;
        }

        public override bool Equals(object obj)
        {
            if (obj is BeliefState)
            {
                BeliefState bs = (BeliefState)obj;
                if (bs.m_lObserved.Count != m_lObserved.Count)
                    return false;
                if (bs.m_lHiddenFormulas.Count != m_lHiddenFormulas.Count)
                    return false;
                foreach (Predicate p in bs.Observed)
                    if (!m_lObserved.Contains(p))
                        return false;
                foreach (Formula f in bs.m_lHiddenFormulas)
                    if (!m_lHiddenFormulas.Contains(f))
                        return false;
                return true;
            }


            return false;
        }

        public bool Contains(Formula f)
        {
            return f.ContainedIn(Observed, true);
        }

        private bool AllObserved(Formula f)
        {
            if (f is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)f).Predicate;
                if (Observed.Contains(p))
                    return true;
                return false;
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                bool bObserved = false;
                foreach (Formula fOperand in cf.Operands)
                {
                    bObserved = AllObserved(fOperand);
                    if (cf.Operator == "or" && bObserved)
                        return true;
                    if (cf.Operator == "and" && !bObserved)
                        return false;
                }
                return cf.Operator == "and";
            }
        }

        public virtual BeliefState Clone()
        {
            return new BeliefState(this);
        }
        public static TimeSpan tsTotalTime = new TimeSpan();

        private bool Contains(CompoundFormula cf)
        {
            ISet<Predicate> lPredicates = cf.GetAllPredicates();
            Predicate pCanonical = null;
            foreach (Predicate p in lPredicates)
            {
                pCanonical = p.Canonical();
                if (!m_dMapPredicatesToFormulas.ContainsKey((GroundedPredicate)pCanonical))
                    return false;
            }
            List<int> lFormulas = m_dMapPredicatesToFormulas[(GroundedPredicate)pCanonical];
            foreach (int idx in lFormulas)
                if (m_lHiddenFormulas[idx] != null && m_lHiddenFormulas[idx].Equals(cf))
                    return true;
            return false;
        }


        public HashSet<Predicate> AddReasoningFormula(Formula f, HashSet<int> hsModifiedClauses)
        {
            DateTime dtStart = DateTime.Now;
            bool bLearnedNewPredicate = false;
            HashSet<Predicate> lAllLearnedPredicates = new HashSet<Predicate>();
            List<PredicateFormula> lLearnedPredicates = new List<PredicateFormula>();
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f.ToCNF();
                List<CompoundFormula> lFormulas = new List<CompoundFormula>();
                if (cf.Operator == "and")
                {
                    foreach (Formula fSub in cf.Operands)
                    {
                        if (fSub is PredicateFormula)
                            lLearnedPredicates.Add((PredicateFormula)fSub);
                        else
                            lFormulas.Add((CompoundFormula)fSub);
                    }
                }
                else
                {
                    lFormulas.Add(cf);
                }

                foreach (CompoundFormula cfSub in lFormulas)
                {
                    if (!Contains(cfSub))
                    {
                        AddInitialStateFormula(cfSub);
                    }
                    m_cfCNFHiddenState.SimpleAddOperand(cfSub);
                }
            }
            else
            {
                lLearnedPredicates.Add((PredicateFormula)f);
            }
            int cIndexes = 0, cValidIndexes = 0, cLearned = 0;
            DateTime dt1 = DateTime.Now;
            TimeSpan ts1 = new TimeSpan(0), ts2 = new TimeSpan(0), ts3 = new TimeSpan(0);


            int cReductions = 0;
            while (lLearnedPredicates.Count > 0)
            {
                bLearnedNewPredicate = true;
                HashSet<int> lIndexes = new HashSet<int>();
                HashSet<Predicate> lKnown = new HashSet<Predicate>();
                foreach (PredicateFormula pf in lLearnedPredicates)
                {
                    GroundedPredicate p = (GroundedPredicate)pf.Predicate.Canonical();
                    if (AddObserved(pf.Predicate))
                    {
                        lAllLearnedPredicates.Add(pf.Predicate);
                        cLearned++;
                    }
                    lKnown.Add(pf.Predicate);

                    if (m_dMapPredicatesToFormulas.ContainsKey(p))
                    {
                        List<int> lFormulas = m_dMapPredicatesToFormulas[p];
                        foreach (int idx in lFormulas)
                            lIndexes.Add(idx);
                        m_dMapPredicatesToFormulas[p] = new List<int>();
                    }
                }
                DateTime dt2 = DateTime.Now;
                ts1 += dt2 - dt1;
                dt1 = dt2;
                lLearnedPredicates = new List<PredicateFormula>();
                foreach (int idx in lIndexes)
                {
                    cIndexes++;
                    CompoundFormula cfPrevious = m_lHiddenFormulas[idx];

                    if (cfPrevious != null)
                    {
                        hsModifiedClauses.Add(idx);
                        cValidIndexes++;

                        DateTime dt3 = DateTime.Now;
                        Formula fNew = cfPrevious.Reduce(lKnown);
                        cReductions++;


                        ts2 += DateTime.Now - dt3;

                        if (fNew is PredicateFormula)
                        {
                            m_lHiddenFormulas[idx] = null;
                            if (!fNew.IsTrue(null))
                                lLearnedPredicates.Add((PredicateFormula)fNew);
                        }
                        else
                        {
                            CompoundFormula cfNew = (CompoundFormula)fNew;
                            if (cfNew.IsSimpleConjunction())
                            {
                                foreach (PredicateFormula pf in cfNew.Operands)
                                {
                                    if (!fNew.IsTrue(null))
                                        lLearnedPredicates.Add(pf);
                                }
                                m_lHiddenFormulas[idx] = null;
                            }
                            else
                                m_lHiddenFormulas[idx] = cfNew;
                        }
                    }
                }
                dt2 = DateTime.Now;
                ts3 += dt2 - dt1;
                dt1 = dt2;

            }




            TimeSpan tsCurrent = DateTime.Now - dtStart;
            tsTotalTime += tsCurrent;
            //Debug.WriteLine("AddReasoningFormula: indexes " + cIndexes + ", valid " + cValidIndexes + ", learned " + cLearned + " time " + tsCurrent.TotalSeconds);
            //Debug.WriteLine(cReductions + ", " + ts1.TotalSeconds + ", " + ts2.TotalSeconds + ", " + ts3.TotalSeconds);
            return lAllLearnedPredicates;
        }

        public int NextNonDetChoice()
        {
            int idx = m_cNonDetChoices;
            //Debug.WriteLine("bs" + ID + " non det " + idx);
            m_cNonDetChoices++;
            return idx;
        }

        public HashSet<Predicate> AddReasoningFormulaEfficient(Formula f)
        {
            throw new NotImplementedException();
            DateTime dtStart = DateTime.Now;
            List<Predicate> lAllLearnedPredicates = new List<Predicate>();
            bool bLearnedNewPredicate = false;
            List<PredicateFormula> lLearnedPredicates = new List<PredicateFormula>();
            if (f is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)f;
                List<CompoundFormula> lFormulas = new List<CompoundFormula>();
                if (cf.Operator == "and")
                {
                    foreach (Formula fSub in cf.Operands)
                    {
                        if (fSub is PredicateFormula)
                        {
                            PredicateFormula pf = (PredicateFormula)fSub;
                            lLearnedPredicates.Add(pf);
                            lAllLearnedPredicates.Add(pf.Predicate);
                        }
                        else
                            lFormulas.Add((CompoundFormula)fSub);
                    }
                }
                else
                {
                    lFormulas.Add(cf);
                }

                foreach (CompoundFormula cfSub in lFormulas)
                {
                    if (!Contains(cfSub))
                    {
                        AddInitialStateFormula(cfSub);
                    }
                    m_cfCNFHiddenState.SimpleAddOperand(cfSub);
                }
            }
            else
            {
                lLearnedPredicates.Add((PredicateFormula)f);
            }
            int cIndexes = 0, cValidIndexes = 0, cLearned = 0;
            //DateTime dt1 = DateTime.Now;
            //TimeSpan ts1 = new TimeSpan(0), ts2 = new TimeSpan(0), ts3 = new TimeSpan(0);
            int cReductions = 0;
            while (lLearnedPredicates.Count > 0)
            {
                bLearnedNewPredicate = true;
                List<Predicate> lKnown = new List<Predicate>();
                List<int> lKnownAssignments = new List<int>();
                HashSet<int> lIndexes = new HashSet<int>();
                foreach (PredicateFormula pf in lLearnedPredicates)
                {
                    GroundedPredicate pCanonical = (GroundedPredicate)pf.Predicate.Canonical();
                    if (AddObserved(pf.Predicate))
                        cLearned++;
                    lKnown.Add(pf.Predicate);
                    if (m_dMapPredicatesToIndexes.ContainsKey(pCanonical))
                    {
                        int iPredicateIndex = m_dMapPredicatesToIndexes[(GroundedPredicate)pCanonical];
                        if (pf.Predicate.Negation)
                            lKnownAssignments.Add(iPredicateIndex * 2 + 1);
                        else
                            lKnownAssignments.Add(iPredicateIndex * 2);

                        List<int> lFormulas = m_dMapPredicateToEfficientFormula[iPredicateIndex];
                        if (lFormulas != null)
                        {
                            foreach (int idx in lFormulas)
                                lIndexes.Add(idx);
                        }
                        m_dMapPredicateToEfficientFormula[iPredicateIndex] = null;
                    }
                }

                //DateTime dt2 = DateTime.Now;
                //ts1 += dt2 - dt1;
                //dt1 = dt2;
                lLearnedPredicates = new List<PredicateFormula>();
                List<int> lNewAssignments = new List<int>();
                foreach (int idx in lIndexes)
                {
                    cIndexes++;
                    EfficientFormula efCurrent = m_lEfficientHidden[idx];
                    if (efCurrent != null && !efCurrent.IsTrue() && !efCurrent.IsFalse())
                    {
                        cValidIndexes++;
                        //DateTime dt3 = DateTime.Now;
                        foreach (int iAssignment in lKnownAssignments)
                        {
                            int iPredicate = iAssignment / 2;
                            bool bPositive = iAssignment % 2 == 0;
                            if (efCurrent.Reduce(iPredicate, bPositive, lNewAssignments))
                            {
                                //not sure what to do here
                                m_lEfficientHidden[idx] = null;
                                break;
                            }
                        }


                        cReductions++;
                        //ts2 += DateTime.Now - dt3;
                    }
                }
                foreach (int iAssignment in lNewAssignments)
                {
                    int iPredicate = iAssignment / 2;

                    GroundedPredicate p = new GroundedPredicate(m_dMapIndexToPredicate[iPredicate]);
                    if (iAssignment % 2 == 1)
                        p = (GroundedPredicate)p.Negate();
                    lLearnedPredicates.Add(new PredicateFormula(p));
                    lAllLearnedPredicates.Add(p);
                    //Debug.WriteLine("Learned: " + p);

                }

                //dt2 = DateTime.Now;
                //ts3 += dt2 - dt1;
                //dt1 = dt2;

            }


            //TimeSpan tsCurrent = DateTime.Now - dtStart;
            //tsTotalTime += tsCurrent;
            //Debug.WriteLine("AddReasoningFormula: indexes " + cIndexes + ", valid " + cValidIndexes + ", learned " + cLearned + " time " + tsCurrent.TotalSeconds);
            //Debug.WriteLine(cReductions + ", " + ts1.TotalSeconds + ", " + ts2.TotalSeconds + ", " + ts3.TotalSeconds);
            /*
            List<int> lRegularFormulaIndexes = new List<int>();
            foreach (Predicate p in lAllLearnedPredicates)
            {
                GroundedPredicate pCanonical = (GroundedPredicate)p.Canonical();
                if (m_dMapPredicatesToFormulas.ContainsKey(pCanonical))
                {
                    List<int> lFormulas = m_dMapPredicatesToFormulas[pCanonical];
                    foreach (int idx in lFormulas)
                        lIndexes.Add(idx);
                    m_dMapPredicatesToFormulas[pCanonical] = new List<int>();
                }
            }
            */


            //BUGBUG: need to implement returning all learned predicates
            return null;
        }

        public void AddInitialStateFormula(CompoundFormula cf)
        {

            if (false && !cf.IsSimpleFormula())
            {
                CompoundFormula cfCNF = (CompoundFormula)cf.ToCNF();
                foreach (CompoundFormula cfSub in cfCNF.Operands)
                    AddInitialStateFormula(cfSub);
                return;
            }

            m_lOriginalHiddenFormulas.Add(cf);
            m_lHiddenFormulas.Add((CompoundFormula)cf);
            EfficientFormula ef = new EfficientFormula(cf.Operator);
            ef.OriginalFormula = cf;
            m_lEfficientHidden.Add(ef);
            ISet<Predicate> lHidden = cf.GetAllPredicates();
            foreach (Predicate p in lHidden)
            {
                GroundedPredicate pCanonical = (GroundedPredicate)p.Canonical();
                if (!Unknown.Contains(pCanonical))
                    Unknown.Add(pCanonical);
                if (!m_dMapPredicatesToFormulas.ContainsKey(pCanonical))
                {
                    m_dMapPredicatesToFormulas[pCanonical] = new List<int>();

                    int iIndex = m_dMapIndexToPredicate.Count;
                    m_dMapIndexToPredicate.Add(pCanonical);
                    m_dMapPredicatesToIndexes[pCanonical] = iIndex;
                    m_dMapPredicateToEfficientFormula.Add(new List<int>());
                }

                int iPredicate = m_dMapPredicatesToIndexes[pCanonical];

                ef.SetVariableValue(iPredicate, !p.Negation);
                m_dMapPredicateToEfficientFormula[iPredicate].Add(m_lEfficientHidden.Count - 1);

                m_dMapPredicatesToFormulas[pCanonical].Add(m_lHiddenFormulas.Count - 1);

            }




            m_cfCNFHiddenState.AddOperand(cf);
            if (!cf.IsSimpleConjunction() && !cf.IsSimpleOneOf() && Options.EnforceCNF)
            {

                m_cfCNFHiddenState = (CompoundFormula)m_cfCNFHiddenState.ToCNF();
            }
        }

        public List<string> Reasoned = new List<string>();
        private void AddReasonedPredicate(Predicate p)
        {
            if (p == Utilities.TRUE_PREDICATE)
                return;
            Debug.Assert(p != Utilities.FALSE_PREDICATE, "Adding P_FALSE to the state");
            if (!m_lObserved.Contains(p))
            {
                if (p.Name != "Choice" && UnderlyingEnvironmentState != null)
                {
                    if (p.Negation)
                        Debug.Assert(!UnderlyingEnvironmentState.Predicates.Contains(p.Negate()), "Adding the negation of a state variable");
                    else
                        Debug.Assert(UnderlyingEnvironmentState.Predicates.Contains(p), "Adding the negation of a state variable");
                }
                AddObserved(p);
                Debug.WriteLine("Reasoned: " + p);
                Reasoned.Add(p.ToString());
            }
        }
        /*
        public bool ApplyReasoning()
        {
            bool bChanged = true, bReasoned = false;
            while (bChanged)
            {
                bugbug;
                bChanged = false;
                List<CompoundFormula> lNew = new List<CompoundFormula>();

                foreach (CompoundFormula cf in m_lHiddenFormulas)
                {
                    CompoundFormula cfCopy = new CompoundFormula(cf);
                    Formula fAfter = cfCopy.Reduce(Observed);
                    if (fAfter != null)
                    {
                        if (fAfter is CompoundFormula)
                        {
                            CompoundFormula cfAfter = (CompoundFormula)fAfter;
                            if (cfAfter.Operator == "and")
                            {
                                foreach (Formula fOperand in cfAfter.Operands)
                                {
                                    if (fOperand is PredicateFormula)
                                    {
                                        AddReasonedPredicate(((PredicateFormula)fOperand).Predicate);
                                        bChanged = true;
                                    }
                                    else
                                        lNew.Add((CompoundFormula)fOperand);
                                }
                            }
                            else
                                lNew.Add(cfAfter);
                        }
                        else
                        {
                            AddReasonedPredicate(((PredicateFormula)fAfter).Predicate);
                            bChanged = true;
                        }
                    }

                }
                if (bChanged)
                    bReasoned = true;
                m_lHiddenFormulas = lNew;
            }
            return bReasoned;
        }
        public bool ApplyReasoningII()
        {
            bool bChanged = true, bReasoned = false;
            while (bChanged)
            {
                bChanged = false;
                List<CompoundFormula> lNew = new List<CompoundFormula>();

                foreach (CompoundFormula cf in m_lHiddenFormulas)
                {
                    CompoundFormula cfCopy = new CompoundFormula(cf);
                    Formula fAfter = cfCopy.Reduce(Observed);
                    if (fAfter != null)
                    {
                        if (fAfter is CompoundFormula)
                        {
                            CompoundFormula cfAfter = (CompoundFormula)fAfter;
                            if (cfAfter.Operator == "and")
                            {
                                foreach (Formula fOperand in cfAfter.Operands)
                                {
                                    if (fOperand is PredicateFormula)
                                    {
                                        AddReasonedPredicate(((PredicateFormula)fOperand).Predicate);
                                        bChanged = true;
                                    }
                                    else
                                        lNew.Add((CompoundFormula)fOperand);
                                }
                            }
                            else
                                lNew.Add(cfAfter);
                        }
                        else
                        {
                            AddReasonedPredicate(((PredicateFormula)fAfter).Predicate);
                            bChanged = true;
                        }
                    }

                }
                if (bChanged)
                    bReasoned = true;
                m_lHiddenFormulas = lNew;
            }
            return bReasoned;
        }
        */
        public override string ToString()
        {
            foreach (Predicate p in Observed)
                if (p.Name == "at" && !p.Negation)
                    return p.ToString();
            return "";
        }
        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        public State ChooseState(bool bRemoveNegativePredicates)
        {
            State s = new State(Problem);
            ISet<Predicate> lAssignment = null;
            Debug.Write("Choosing hidden variables ");
            while (lAssignment == null)
            {
                Debug.Write(".");
                lAssignment = ChooseHiddenPredicates(m_lHiddenFormulas, true);
            }
            Debug.WriteLine("");
            foreach (Predicate p in lAssignment)
            {
                s.AddPredicate(p);
            }
            foreach (GroundedPredicate p in m_lObserved)
            {
                s.AddPredicate(p);
            }
            if (bRemoveNegativePredicates)
                s.RemoveNegativePredicates();
            if (UnderlyingEnvironmentState == null)
                UnderlyingEnvironmentState = s;
            return s;
        }

        public State ChooseState(bool bRemoveNegativePredicates, bool bChooseDeadend)
        {
            State s = new State(Problem);
            if (UnderlyingEnvironmentState != null)
            {
                if (Problem.Name.Contains("Large"))
                    throw new NotImplementedException();
                else
                {
                    ISet<Predicate> lAssignment = null;
                    Debug.Write("Choosing hidden variables ");
                    while (lAssignment == null)
                    {
                        Debug.Write(".");
                        if (bChooseDeadend)
                        {
                            int idx = RandomGenerator.Next(Problem.DeadEndList.Count);
                            if (idx >= Problem.DeadEndList.Count)
                                Console.Write("*");
                            Formula f = Problem.DeadEndList[idx];
                            ISet<Predicate> hsDeadendPredicates = f.GetAllPredicates();
                            ISet<Predicate> lDeadendPredicates = new HashSet<Predicate>(hsDeadendPredicates);
                            lAssignment = ChooseHiddenPredicatesForDeadendDetection(m_lHiddenFormulas, lDeadendPredicates, false);
                        }
                        else
                        {
                            List<CompoundFormula> lHidden = new List<CompoundFormula>(m_lHiddenFormulas);
                            CompoundFormula cfAnd = new CompoundFormula("and");

                            foreach (Formula f in Problem.DeadEndList)
                            {
                                Formula fReduced = f.Reduce(Observed);
                                if (fReduced is CompoundFormula)
                                    lHidden.Add((CompoundFormula)fReduced.Negate());
                                else
                                    cfAnd.AddOperand(fReduced.Negate());
                            }
                            if (cfAnd.Operands.Count > 0)
                                lHidden.Add(cfAnd);

                            lAssignment = ChooseHiddenPredicates(lHidden, true);

                        }
                    }
                    Debug.WriteLine("");
                    foreach (Predicate p in lAssignment)
                    {
                        s.AddPredicate(p);
                    }
                    foreach (GroundedPredicate p in m_lObserved)
                    {
                        s.AddPredicate(p);
                    }
                }
            }
            
            if (bRemoveNegativePredicates)
                s.RemoveNegativePredicates();
            if (UnderlyingEnvironmentState == null)
                UnderlyingEnvironmentState = s;
            return s;
        }


        private int GetRandomUniquePosition(List<int> lPositions, int iSize)
        {
            while (true)
            {
                int x = RandomGenerator.Next(iSize) + 1;
                int y = RandomGenerator.Next(iSize) + 1;
                int pos = y * 1000 + x;
                if (!lPositions.Contains(pos))
                {
                    lPositions.Add(pos);
                    return pos;
                }
            }
        }

        private List<CompoundFormula> Reduce(List<CompoundFormula> lHidden, ISet<Predicate> lAssignment, ISet<Predicate> lUnknown)
        {
            List<CompoundFormula> lReduced = new List<CompoundFormula>();
            bool bAssignmentChanged = false;
            foreach (CompoundFormula cf in lHidden)
            {
                if (cf != null)
                {
                    Formula fReduced = cf.Reduce(lAssignment);
                    if (fReduced.IsFalse(lAssignment))
                        return null;
                    if (fReduced is PredicateFormula)
                    {
                        Predicate pReasoned = ((PredicateFormula)fReduced).Predicate;
                        if (pReasoned != Utilities.TRUE_PREDICATE)
                        {
                            if (lAssignment.Contains(pReasoned.Negate()))
                                return null;
                            if (!lAssignment.Contains(pReasoned))
                            {
                                lAssignment.Add(pReasoned);
                                lUnknown.Remove(pReasoned);
                                lUnknown.Remove(pReasoned.Negate());
                                bAssignmentChanged = true;
                            }
                        }
                    }
                    else
                    {
                        CompoundFormula cfReduced = (CompoundFormula)fReduced;
                        if (cfReduced.Operator == "and")
                        {
                            CompoundFormula cfAnd = new CompoundFormula("and");
                            foreach (Formula fSub in cfReduced.Operands)
                            {
                                if (fSub is PredicateFormula)
                                {
                                    Predicate pReasoned = ((PredicateFormula)fSub).Predicate;
                                    if (pReasoned != Utilities.TRUE_PREDICATE)
                                    {

                                        if (lAssignment.Contains(pReasoned.Negate()))
                                            return null;
                                        if (!lAssignment.Contains(pReasoned))
                                        {
                                            lAssignment.Add(pReasoned);
                                            lUnknown.Remove(pReasoned);
                                            lUnknown.Remove(pReasoned.Negate());
                                            bAssignmentChanged = true;
                                        }
                                    }
                                }
                                else
                                    cfAnd.AddOperand(fSub);
                            }
                            if (cfAnd.Operands.Count == 1)
                                lReduced.Add((CompoundFormula)cfAnd.Operands[0]);
                            else if (cfAnd.Operands.Count > 1)
                                lReduced.Add(cfAnd);
                        }
                        else
                        {
                            lReduced.Add(cfReduced);
                        }
                    }
                }
            }
            if (bAssignmentChanged)
                return Reduce(lReduced, lAssignment, lUnknown);
            else
                return lReduced;
        }

        private List<CompoundFormula> AddAssignment(List<CompoundFormula> lHidden, ISet<Predicate> lAssignment, ISet<Predicate> lUnknown, Predicate pAssignment)
        {
            if (lAssignment.Contains(pAssignment.Negate()))
                return null;
            lUnknown.Remove(pAssignment.Canonical());
            lAssignment.Add(pAssignment);
            return Reduce(lHidden, lAssignment, lUnknown);
        }
        
        private T ElementAt<T>(ISet<T> set, int index)
        {
            foreach(T t in set)
            {
                if(index == 0)
                    return t;
                index--;

            }
            return default(T);
        }

        private ISet<Predicate> ChooseHiddenPredicates(ISet<Predicate> lAssignment, ISet<Predicate> lUnknown, int iCurrent)
        {
            if (iCurrent == lUnknown.Count)
                return lAssignment;
            Predicate pCurrent = ElementAt<Predicate>(lUnknown, iCurrent);
            bool bValid = true;
            if (RandomGenerator.NextDouble() < 0.5)
                pCurrent = pCurrent.Negate();
            lAssignment.Add(pCurrent);
            ISet<Predicate> lFullAssignment = null;
            //trying p
            foreach (CompoundFormula cfHidden in m_lHiddenFormulas)
            {
                if (cfHidden.IsFalse(lAssignment))
                {
                    bValid = false;
                    break;
                }
            }
            if (bValid)
                lFullAssignment = ChooseHiddenPredicates(lAssignment, lUnknown, iCurrent + 1);
            if (lFullAssignment != null)
                return lFullAssignment;
            //now trying ~p
            lAssignment.Remove(pCurrent);
            lAssignment.Add(pCurrent.Negate());
            bValid = true;
            foreach (CompoundFormula cfHidden in m_lHiddenFormulas)
                if (cfHidden.IsFalse(lAssignment))
                {
                    bValid = false;
                    break;
                }
            if (bValid)
                lFullAssignment = ChooseHiddenPredicates(lAssignment, lUnknown, iCurrent + 1);
            return lFullAssignment;
        }

        private List<CompoundFormula> RemoveOneOf(List<CompoundFormula> lHidden)
        {
            List<CompoundFormula> lClean = new List<CompoundFormula>();
            foreach (CompoundFormula cf in lHidden)
            {
                if (cf.Operator == "oneof")
                {
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    int idx = RandomGenerator.Next(cf.Operands.Count);
                    cfAnd.AddOperand(cf.Operands[idx]);
                    for (int i = 0; i < cf.Operands.Count; i++)
                    {
                        if (i != idx)
                            cfAnd.AddOperand(cf.Operands[i].Negate());
                    }
                    lClean.Add(cfAnd);
                }
                else
                {
                    lClean.Add(cf);
                }
            }
            return lClean;
        }

        private ISet<Predicate> ChooseHiddenPredicates(List<CompoundFormula> lHidden, bool bCheatUsingAt)
        {
            return ChooseHiddenPredicates(lHidden, null, bCheatUsingAt);
        }
        private ISet<Predicate> ChooseHiddenPredicatesForDeadendDetection(List<CompoundFormula> lHidden, ISet<Predicate> lDeadendPredicates, bool bPreconditionFailure)
        {
            HashSet<Predicate> lAllPredicates = new HashSet<Predicate>();
 
            foreach (CompoundFormula f in lHidden)
            {
                if (f != null)
                {
                    f.GetAllPredicates(lAllPredicates);
                }
            }

            HashSet<Predicate> lToAssign = new HashSet<Predicate>();
            foreach (Predicate p in lAllPredicates)
            {
                lToAssign.Add(p.Canonical());
            }

            ISet<Predicate> lInitialAssignment = new HashSet<Predicate>();
            foreach (Predicate pDeadend in lDeadendPredicates)
            {
                lToAssign.Remove(pDeadend.Canonical());
                //lInitialAssignment.Add(pDeadend);
            }



            //ApplySimpleOneOfs(lOneOfs, lInitialAssignment, lCanonicalPredicates);

            ISet<Predicate> lAssignment = null;
            lAssignment = ChooseHiddenPredicatesForDeadendDetection(lHidden, lInitialAssignment, lToAssign, lDeadendPredicates, bPreconditionFailure);
            return lAssignment;
        }


        private ISet<Predicate> GetHiddenPredicates(List<CompoundFormula> lHidden)
        {
            HashSet<Predicate> lAllPredicates = new HashSet<Predicate>();
            HashSet<Predicate> lOneoffPredicates = new HashSet<Predicate>();
            List<CompoundFormula> lOneOfs = new List<CompoundFormula>();
            foreach (CompoundFormula f in lHidden)
            {
                if (f != null)
                {
                    if (f.IsSimpleOneOf())
                    {
                        lOneOfs.Add(f);
                        f.GetAllPredicates(lOneoffPredicates);
                    }
                    else
                        f.GetAllPredicates(lAllPredicates);
                }
            }
            List<Predicate> lCanonicalPredicates = new List<Predicate>();
            List<Predicate> lCanonicalOneofPredicates = new List<Predicate>();
            foreach (Predicate p in lAllPredicates)
            {
                Predicate pCanonical = p.Canonical();
                if (!lCanonicalPredicates.Contains(pCanonical))
                    lCanonicalPredicates.Add(pCanonical);

            }
            foreach (Predicate p in lOneoffPredicates)
            {
                Predicate pCanonical = p.Canonical();
                if (!lCanonicalOneofPredicates.Contains(pCanonical))
                    lCanonicalOneofPredicates.Add(pCanonical);

            }
            if (!Options.ComputeCompletePlanTree)
            {
                lCanonicalPredicates = Permute(lCanonicalPredicates);
                lCanonicalOneofPredicates = Permute(lCanonicalOneofPredicates);
            }
            ISet<Predicate> lToAssign = new HashSet<Predicate>();
            foreach (Predicate p in lCanonicalOneofPredicates)
                if (!Problem.Domain.AlwaysKnown(p) && !lToAssign.Contains(p))
                    lToAssign.Add(p);
            foreach (Predicate p in lCanonicalPredicates)
                if (!Problem.Domain.AlwaysKnown(p) && !lToAssign.Contains(p))
                    lToAssign.Add(p);
            return lToAssign;
        }

        private ISet<Predicate> ChooseHiddenPredicates(List<CompoundFormula> lHidden, List<ISet<Predicate>> lCurrentAssignments, bool bCheatUsingAt)
        {
            ISet<Predicate> lToAssign = GetHiddenPredicates(lHidden);

            HashSet<Predicate> lInitialAssignment = new HashSet<Predicate>();
            if (false && bCheatUsingAt)
                CheatUsingAtPredicate(lToAssign, lInitialAssignment);

            //ApplySimpleOneOfs(lOneOfs, lInitialAssignment, lCanonicalPredicates);

            ISet<Predicate> lAssignment = null;
            if (lCurrentAssignments == null)
                lAssignment = ChooseHiddenPredicates(lHidden, lInitialAssignment, lToAssign);
            else
            {
                lAssignment = SimpleChooseHiddenPredicates(new List<Formula>(lHidden), new HashSet<Predicate>(lInitialAssignment), lToAssign, lCurrentAssignments, false);
                if (lAssignment == null)
                    lAssignment = ChooseHiddenPredicates(lHidden, lInitialAssignment, lToAssign, lCurrentAssignments);
            }

            return lAssignment;
        }
        /*
        private List<Predicate> ChooseHiddenPredicates(List<CompoundFormula> lHidden, List<List<Predicate>> lCurrentAssignments)
        {
            HashSet<Predicate> lAllPredicates = new HashSet<Predicate>();
            foreach (CompoundFormula f in lHidden)
            {
                if( f != null)
                    f.GetAllPredicates(lAllPredicates);
            }
            List<Predicate> lCanonicalPredicates = new List<Predicate>();
            foreach (Predicate p in lAllPredicates)
            {
                if (!p.Negation)
                {
                    if (!lCanonicalPredicates.Contains(p))
                        lCanonicalPredicates.Add(p);
                }
                else
                {
                    Predicate pNegate = p.Negate();
                    if (!lCanonicalPredicates.Contains(pNegate))
                        lCanonicalPredicates.Add(pNegate);
                }
            }

            List<Predicate> lInitialAssignment = new List<Predicate>();

            List<Predicate> lAssignment = ChooseHiddenPredicates(lHidden, lInitialAssignment, lCanonicalPredicates, lCurrentAssignments);
            return lAssignment;
        }*/

        //doesn't work - need to correlate between oneofs...
        private void ApplySimpleOneOfs(List<CompoundFormula> lOneOfs, List<Predicate> lInitialAssignment, List<Predicate> lCanonicalPredicates)
        {
            foreach (CompoundFormula cf in lOneOfs)
            {
                List<Predicate> lUnassignedPredicates = new List<Predicate>();
                bool bAlreadyTrue = false;
                foreach (PredicateFormula pf in cf.Operands)
                {
                    if (lCanonicalPredicates.Contains(pf.Predicate))
                    {
                        lUnassignedPredicates.Add(pf.Predicate);
                        lCanonicalPredicates.Remove(pf.Predicate);
                    }
                    if (lCanonicalPredicates.Contains(pf.Predicate.Negate()))
                    {
                        lUnassignedPredicates.Add(pf.Predicate);
                        lCanonicalPredicates.Remove(pf.Predicate.Negate());
                    }
                    if (lInitialAssignment.Contains(pf.Predicate))
                        bAlreadyTrue = true;
                }
                if (!bAlreadyTrue)
                {
                    int idx = RandomGenerator.Next(lUnassignedPredicates.Count);
                    Predicate pTrue = lUnassignedPredicates[idx];
                    lUnassignedPredicates.RemoveAt(idx);
                    lInitialAssignment.Add(pTrue);
                }
                foreach (Predicate p in lUnassignedPredicates)
                    lInitialAssignment.Add(p.Negate());
            }
        }

        private void CheatUsingAtPredicate(ISet<Predicate> lCanonicalPredicates, ISet<Predicate> lInitialAssignment)
        {
            List<Predicate> lValidAt = new List<Predicate>();
            foreach (Predicate p in lCanonicalPredicates)
                if (p.Name == "at")
                    lValidAt.Add(p);
            if (lValidAt.Count > 0)
            {
                int idx = RandomGenerator.Next(lValidAt.Count);
                lInitialAssignment.Add(lValidAt[idx]);
                for (int i = 0; i < lValidAt.Count; i++)
                {
                    if (i != idx)
                        lInitialAssignment.Add(lValidAt[i].Negate());
                    lCanonicalPredicates.Remove(lValidAt[i]);
                }
            }
        }

        private List<Predicate> Permute(List<Predicate> lPredicates)
        {
            List<Predicate> lPermutation = new List<Predicate>();
            while (lPredicates.Count > 0)
            {
                int idx = RandomGenerator.Next(lPredicates.Count);
                lPermutation.Add(lPredicates[idx]);
                lPredicates.RemoveAt(idx);

            }
            return lPermutation;
        }

        private Predicate GetNonDiversePredicate(ISet<Predicate> lUnknown, List<ISet<Predicate>> lCurrentAssignments, out bool bAllTrue, out bool bAllFalse)
        {
            bAllTrue = true;
            bAllFalse = true;

            if (lCurrentAssignments.Count == 0)
            {
                bAllTrue = false;//choosing true first is better in some domains
                bAllFalse = false;//but not in others...
                return lUnknown.First();//the order of the variables is already randomized - might as well return the first one. This is important because oneofs appear first.
                //return lUnknown[RandomGenerator.Next(lUnknown.Count)]; the order of the variables is already randomized - miFF.Search.gHt as well return the first one. This is important because oneofs appear first.
            }
            List<Predicate>[] alPredicates = new List<Predicate>[3];
            alPredicates[0] = new List<Predicate>();
            alPredicates[1] = new List<Predicate>();
            alPredicates[2] = new List<Predicate>();
            foreach (Predicate p in lUnknown)
            {
                bAllTrue = true;
                bAllFalse = true;
                foreach (ISet<Predicate> lAssignment in lCurrentAssignments)
                {
                    if (lAssignment.Contains(p))
                        bAllFalse = false;
                    else
                        bAllTrue = false;
                    if (!bAllTrue && !bAllFalse)
                        break;
                }
                if (bAllTrue)
                    alPredicates[0].Add(p);
                if (bAllFalse)
                    alPredicates[1].Add(p);
                if (!bAllFalse && !bAllTrue)
                    alPredicates[2].Add(p);
                // if (bAllFalse || bAllTrue)
                //    return p;
            }
            if (alPredicates[0].Count > 0)
            {
                bAllTrue = true;
                bAllFalse = false;
                return alPredicates[0][0];//the order of the variables is already randomized - miFF.Search.gHt as well return the first one. This is important because oneofs appear first.
                //return alPredicates[0][RandomGenerator.Next(alPredicates[0].Count)];
            }
            if (alPredicates[1].Count > 0)
            {
                bAllTrue = false;
                bAllFalse = true;
                return alPredicates[1][0];//the order of the variables is already randomized - miFF.Search.gHt as well return the first one. This is important because oneofs appear first.
                //return alPredicates[1][RandomGenerator.Next(alPredicates[1].Count)];
            }
            if (alPredicates[2].Count > 0)
            {
                bAllTrue = false;
                bAllFalse = false;
                return alPredicates[2][0];//the order of the variables is already randomized - miFF.Search.gHt as well return the first one. This is important because oneofs appear first.
                //return alPredicates[2][RandomGenerator.Next(alPredicates[2].Count)];
            }
            return lUnknown.First();
        }
        private ISet<Predicate> SimpleChooseHiddenPredicates(List<Formula> lHidden, HashSet<Predicate> lAssignment, ISet<Predicate> lUnknown, List<ISet<Predicate>> lCurrentAssignments, bool random)
        {
            while (lUnknown.Count > 0)
            {
                bool bAllTrue = false, bAllFalse = false;
                Predicate pCurrent = GetNonDiversePredicate(lUnknown, lCurrentAssignments, out bAllTrue, out bAllFalse);
                lUnknown.Remove(pCurrent);
                if (bAllTrue)
                    pCurrent = pCurrent.Negate();
                else if (!bAllFalse && !Options.ComputeCompletePlanTree && RandomGenerator.NextDouble() < 0.5 && random)
                {
                    pCurrent = pCurrent.Negate();
                }
                lHidden.Add(new PredicateFormula(pCurrent));

                bool bValid = ApplyUnitPropogation(lHidden, lAssignment);
                if (!bValid)
                    return null;
                //List<CompoundFormula> lReduced = AddAssignment(lHidden, lNewAssignment, lNewUnknown, pCurrent);
                foreach (Predicate p in lAssignment)
                    lUnknown.Remove(p.Canonical());
            }
            return new HashSet<Predicate>(lAssignment);
        }

        private ISet<Predicate> ChooseHiddenPredicates(List<CompoundFormula> lHidden, ISet<Predicate> lAssignment, ISet<Predicate> lUnknown, List<ISet<Predicate>> lCurrentAssignments)
        {
            if (lHidden == null)
                return null;
            if (lUnknown.Count == 0)
                return lAssignment;//BUGBUG - does not work - need to check why!!
            bool bAllTrue = false, bAllFalse = false;
            Predicate pCurrent = GetNonDiversePredicate(lUnknown, lCurrentAssignments, out bAllTrue, out bAllFalse);
            lUnknown.Remove(pCurrent);
            if (bAllTrue)
                pCurrent = pCurrent.Negate();
            else if (!bAllFalse && !Options.ComputeCompletePlanTree && RandomGenerator.NextDouble() < 0.5)
            {
                pCurrent = pCurrent.Negate();
            }
            ISet<Predicate> lNewHidden = new HashSet<Predicate>(lUnknown);
            ISet<Predicate> lNewAssignment = new HashSet<Predicate>(lAssignment);
            List<CompoundFormula> lReduced = AddAssignment(lHidden, lNewAssignment, lNewHidden, pCurrent);
            ISet<Predicate> lFullAssignment = ChooseHiddenPredicates(lReduced, lNewAssignment, lNewHidden, lCurrentAssignments);
            if (lFullAssignment != null)
                return lFullAssignment;
            lNewHidden = new HashSet<Predicate>(lUnknown);
            lNewAssignment = new HashSet<Predicate>(lAssignment);
            lReduced = AddAssignment(lHidden, lNewAssignment, lNewHidden, pCurrent.Negate());
            lFullAssignment = ChooseHiddenPredicates(lReduced, lNewAssignment, lNewHidden, lCurrentAssignments);
            return lFullAssignment;
        }
        //random
        private ISet<Predicate> ChooseHiddenPredicates(List<CompoundFormula> lHidden, ISet<Predicate> lAssignment, ISet<Predicate> lUnknown, bool bRandomAssignment = true)
        {
            if (lHidden == null)
                return null;
            if (lUnknown.Count == 0)
                return lAssignment;//BUGBUG - does not work - need to check why!!
            ISet<Predicate> lFullAssignment = null;
            Predicate pCurrent = lUnknown.First();
            lUnknown.Remove(pCurrent);
            if (/*bRandomAssignment && */!Options.ComputeCompletePlanTree)
                if (RandomGenerator.NextDouble() < 0.5)
                    pCurrent = pCurrent.Negate();
            ISet<Predicate> lNewHidden = new HashSet<Predicate>(lUnknown);
            ISet<Predicate> lNewAssignment = new HashSet<Predicate>(lAssignment);
            List<CompoundFormula> lReduced = AddAssignment(lHidden, lNewAssignment, lNewHidden, pCurrent);
            if (lReduced != null)
                lFullAssignment = ChooseHiddenPredicates(lReduced, lNewAssignment, lNewHidden, bRandomAssignment);
            if (lFullAssignment != null)
                return lFullAssignment;
            lNewHidden = new HashSet<Predicate>(lUnknown);
            lNewAssignment = new HashSet<Predicate>(lAssignment);
            lReduced = AddAssignment(lHidden, lNewAssignment, lNewHidden, pCurrent.Negate());
            lFullAssignment = ChooseHiddenPredicates(lReduced, lNewAssignment, lNewHidden, bRandomAssignment);
            return lFullAssignment;
        }
        private ISet<Predicate> ChooseHiddenPredicatesForDeadendDetection(List<CompoundFormula> lHidden, ISet<Predicate> lAssignment, ISet<Predicate> lUnknown, ISet<Predicate> lDeadendPredicates, bool bPreconditionFailure)
        {
            ISet<Predicate> lNewHidden = new HashSet<Predicate>(lUnknown);
            ISet<Predicate> lNewAssignment = new HashSet<Predicate>(lAssignment);
            List<CompoundFormula> lReduced = new List<CompoundFormula>();
            foreach (CompoundFormula cf in lHidden)
                if (cf != null)
                    lReduced.Add(cf);
            foreach (Predicate pDeadend in lDeadendPredicates)
            {
                if (!Problem.Domain.AlwaysKnown(pDeadend))
                    lReduced = AddAssignment(lReduced, lNewAssignment, lNewHidden, pDeadend);
            }
            if (false && bPreconditionFailure)//shutting this off - we should not mix precondition failure and deadends
            {
                if (m_lProblematicTag != null)
                {
                    ISet<Predicate> lAssignmentWithProblematic = new HashSet<Predicate>(lNewAssignment);
                    ISet<Predicate> lAssignmentWithOppositeProblematic = new HashSet<Predicate>(lNewAssignment);
                    List<CompoundFormula> lReducedWithProblematic = lHidden;
                    List<CompoundFormula> lReducedWithOppositeProblematic = lHidden;
                    ISet<Predicate> lOppositeProblematicTag = new HashSet<Predicate>();

                    bool bProblematicTagConflictsWithDeadend = false;
                    bool bOppositeProblematicTagConflictsWithDeadend = false;

                    foreach (Predicate p in m_lProblematicTag)
                    {
                        Predicate pNegate = p.Negate();
                        if (lOppositeProblematicTag.Count == 0)
                            lOppositeProblematicTag.Add(pNegate);
                        if (lAssignmentWithProblematic.Contains(pNegate))
                            bProblematicTagConflictsWithDeadend = true;
                        if (!bProblematicTagConflictsWithDeadend)
                            lReducedWithProblematic = AddAssignment(lReducedWithProblematic, lAssignmentWithProblematic, lNewHidden, p);
                        if (lAssignmentWithOppositeProblematic.Contains(p))
                            bOppositeProblematicTagConflictsWithDeadend = true;
                        if (!bOppositeProblematicTagConflictsWithDeadend)
                            lReducedWithOppositeProblematic = AddAssignment(lReducedWithOppositeProblematic, lAssignmentWithOppositeProblematic, lNewHidden, pNegate);
                    }


                    m_lProblematicTag = lOppositeProblematicTag;
                    if (!bOppositeProblematicTagConflictsWithDeadend)
                    {
                        lReduced = lReducedWithOppositeProblematic;
                        lNewAssignment = lAssignmentWithOppositeProblematic;
                    }
                    else if (!bProblematicTagConflictsWithDeadend)
                    {
                        lReduced = lReducedWithProblematic;
                        lNewAssignment = lAssignmentWithProblematic;
                    }
                    else
                    {
                        m_lProblematicTag = null;
                        Debug.WriteLine("*");
                    }
                }
            }

            ISet<Predicate> lFullAssignment = ChooseHiddenPredicates(lReduced, lNewAssignment, lNewHidden, bPreconditionFailure);
            if (lFullAssignment == null)
                throw new NotImplementedException();
            return lFullAssignment;
        }

        private List<Formula> FindObligatory(ISet<Predicate> lAssignment, List<Formula> lOptional)
        {
            List<Formula> lObligatory = new List<Formula>();
            foreach (Formula f in lOptional)
            {
                if (f.IsTrue(lAssignment))
                    lObligatory.Add(f);
            }
            return lObligatory;
        }

        private bool SelectAtLeastOne(ISet<Predicate> lAssignment, List<Formula> lOptional)
        {
            List<Formula> lConsistent = RemoveInconsistencies(lAssignment, lOptional);
            if (lConsistent.Count == 0)
                return false;
            List<Formula> lObligatory = FindObligatory(lAssignment, lConsistent);
            foreach (Formula fObligatory in lObligatory)
            {
                if (fObligatory is PredicateFormula)
                    lAssignment.Add(((PredicateFormula)fObligatory).Predicate);
                else
                    throw new NotImplementedException("Need to implement behavior for compound formulas.");
                lConsistent.Remove(fObligatory);
            }
            if (lConsistent.Count > 0)
            {
                int iTermCount = RandomGenerator.Next(lConsistent.Count) + 1;//n+1 because we want n to be also valid
                while (iTermCount > 0)
                {
                    int iRandomIndex = RandomGenerator.Next(lConsistent.Count);
                    Formula f = lConsistent[iRandomIndex];
                    if (f is PredicateFormula)
                        lAssignment.Add(((PredicateFormula)f).Predicate);
                    else
                    {
                        throw new NotImplementedException("Need to implement behavior for compound formulas.");
                    }
                    lConsistent.RemoveAt(iRandomIndex);
                    iTermCount--;
                }
                //for the rest of the terms - set the value to false
                foreach (Formula f in lConsistent)
                {
                    if (f is PredicateFormula)
                        lAssignment.Add(((PredicateFormula)f).Predicate.Negate());
                    else
                        throw new NotImplementedException("Need to implement behavior for compound formulas.");
                }
            }
            return true;
        }


        private List<Formula> RemoveInconsistencies(ISet<Predicate> lAssignment, List<Formula> lOptional)
        {
            List<Formula> lConsistent = new List<Formula>();
            foreach (Formula f in lOptional)
            {
                if (!f.IsFalse(lAssignment))
                    lConsistent.Add(f);
            }
            return lConsistent;
        }


        public bool IsGoalState()
        {
            return Contains(Problem.Goal);
        }

        private List<State> ApplyActions(List<ISet<Predicate>> lChosen, List<Action> lActions)
        {
            List<State> lCurrent = new List<State>();
            foreach (ISet<Predicate> lState in lChosen)
            {
                State s = new State(Problem);
                foreach (Predicate p in lState)
                    s.AddPredicate(p);
                foreach (Predicate p in Observed)
                    s.AddPredicate(p);
                lCurrent.Add(s);
            }

            List<State> lNext = null;
            foreach (Action a in lActions)
            {
                lNext = new List<State>();
                foreach (State s in lCurrent)
                {
                    State sTag = s.Apply(a);
                    //if (sTag == null)
                    //    sTag = s.Apply(a);
                    lNext.Add(sTag);
                }
                lCurrent = lNext;
            }

            return lCurrent;
        }


        public State WriteTaggedDomainAndProblem(CompoundFormula cfGoal, List<Action> lAppliedActions, out int cTags, out MemoryStream msModels)
        {
            List<ISet<Predicate>> lChosen = ChooseStateSet();
            List<State> lStates = ApplyActions(lChosen, lAppliedActions);

            msModels = null;

            if (lStates.Count == 1)
            {
                MemoryStream msProblem = Problem.WriteSimpleProblem(lStates[0]);
                MemoryStream msDomain = Problem.Domain.WriteSimpleDomain();

                msModels = new MemoryStream();
                StreamWriter sw = new StreamWriter(msModels);
                msDomain.Position = 0;
                StreamReader srDomain = new StreamReader(msDomain);
                sw.Write(srDomain.ReadToEnd());
                sw.Write('\0');
                msProblem.Position = 0;
                StreamReader srProblem = new StreamReader(msProblem);
                sw.Write(srProblem.ReadToEnd());
                sw.Write('\0');
                sw.Flush();

                cTags = 1;
                return lStates[0];
            }

            if (Options.ConsiderStateNegations)
            {
                List<ISet<Predicate>> lAllOthers = new List<ISet<Predicate>>();
                lAllOthers.Add(GetNonAppearingPredicates(lChosen));
                lStates.AddRange(ApplyActions(lAllOthers, lAppliedActions));
            }
            return WriteTaggedDomainAndProblem(cfGoal, lStates, DeadendStrategies.Lazy, out cTags, out msModels);
        }

        public List<ISet<Predicate>> ChosenStates = null;



        public void GetTaggedDomainAndProblem(PartiallySpecifiedState pssCurrent, List<Action> lAppliedActions, 
            Options.DeadendStrategies dsStrategy, bool bPreconditionFailure,
            out int cTags, out Domain dTagged, out Problem pTagged
            )
        {
            cTags = 0;
            List<ISet<Predicate>> lChosen = ChooseStateSet();
            ChosenStates = lChosen;

            dTagged = null;
            pTagged = null;
            if (lChosen == null)
                return;

            //BUGBUG;//We should cache the states, try to avoid this useless repetition
            List<State> lStates = ApplyActions(lChosen, lAppliedActions);

            if(lStates.Count == 0)
            {
                cTags = 1;
                pTagged = Problem;
                dTagged = Problem.Domain;
                return;
            }

            HashSet<Predicate> lObserved = new HashSet<Predicate>();
            Dictionary<string, ISet<Predicate>> dTags = GetTags(lStates, lObserved);

            cTags = dTags.Count;

            if (Options.Translation == Options.Translations.SDR)
            {

                dTagged = Problem.Domain.CreateTaggedDomain(dTags, Problem, null);

            }
            else
                throw new NotImplementedException();


            if (Options.Translation == Options.Translations.SDR)
            {
                pTagged = Problem.CreateTaggedProblem(dTagged, dTags, lObserved, dTags.Values.First(), 
                    lStates.First().FunctionValues, dsStrategy, bPreconditionFailure);
            }
            else
                throw new NotImplementedException();

        }

        public State WriteTaggedDomainAndProblem(PartiallySpecifiedState pssCurrent, List<Action> lAppliedActions, out int cTags, out MemoryStream msModels)
        {
            msModels = null;
            cTags = 0;
            List<ISet<Predicate>> lChosen = ChooseStateSet();
            ChosenStates = lChosen;

            if (lChosen == null)
                return null;

            List<State> lStates = ApplyActions(lChosen, lAppliedActions);


            if (lStates.Count == 1 && !Problem.Domain.ContainsNonDeterministicActions && Options.Translation != Options.Translations.BestCase)
            {
                MemoryStream msProblem = Problem.WriteSimpleProblem(lStates[0]);
                MemoryStream msDomain = Problem.Domain.WriteSimpleDomain(false, false);

                msModels = new MemoryStream();
                StreamWriter sw = new StreamWriter(msModels);
                msDomain.Position = 0;
                StreamReader srDomain = new StreamReader(msDomain);
                sw.Write(srDomain.ReadToEnd());
                sw.Write('\0');
                msProblem.Position = 0;
                StreamReader srProblem = new StreamReader(msProblem);
                sw.Write(srProblem.ReadToEnd());
                sw.Write('\0');
                sw.Flush();

                cTags = 1;
                return lStates[0];
            }

            if (Options.ConsiderStateNegations)
            {
                List<ISet<Predicate>> lAllOthers = new List<ISet<Predicate>>();
                lAllOthers.Add(GetNonAppearingPredicates(lChosen));
                lStates.AddRange(ApplyActions(lAllOthers, lAppliedActions));
            }
            return WriteTaggedDomainAndProblem(pssCurrent, lStates, DeadendStrategies.Lazy, out cTags, out msModels);
        }


        //static int cChoose = 0;
        public State WriteTaggedDomainAndProblemDeadEnd(PartiallySpecifiedState pssCurrent, List<Action> lAppliedActions,
            List<Formula> lMaybeDeadends, DeadendStrategies dsStrategy, bool bPreconditionFailure, out int cTags, out MemoryStream msModels)
        {
            List<ISet<Predicate>> lChosen = null;

            ISet<Predicate> lTemp = m_lProblematicTag;
            //cChoose++;
            //if(cChoose == 34)
            //    Console.Write("*");

            if (bPreconditionFailure)
                lChosen = ChooseStateSet();
            else
                lChosen = ChooseDeadEndState(lMaybeDeadends, dsStrategy, bPreconditionFailure);
            //if (lChosen[1].Count == 1)
            //    Console.Write("*");
            List<State> lStates = ApplyActions(lChosen, lAppliedActions);

            if (lStates == null || lStates[0] == null)
                Debug.Write("*");

            msModels = null;

            if (lStates.Count == 1 && !Problem.Domain.ContainsNonDeterministicActions && Options.Translation != Options.Translations.BestCase)
            {
                MemoryStream msProblem = Problem.WriteSimpleProblem(lStates[0]);
                MemoryStream msDomain = Problem.Domain.WriteSimpleDomain();

                msModels = new MemoryStream();
                StreamWriter sw = new StreamWriter(msModels);
                msDomain.Position = 0;
                StreamReader srDomain = new StreamReader(msDomain);
                sw.Write(srDomain.ReadToEnd());
                sw.Write('\0');
                msProblem.Position = 0;
                StreamReader srProblem = new StreamReader(msProblem);
                sw.Write(srProblem.ReadToEnd());
                sw.Write('\0');
                sw.Flush();

                cTags = 1;
                return lStates[0];
            }

            if (Options.ConsiderStateNegations)
            {
                List<ISet<Predicate>> lAllOthers = new List<ISet<Predicate>>();
                lAllOthers.Add(GetNonAppearingPredicates(lChosen));
                lStates.AddRange(ApplyActions(lAllOthers, lAppliedActions));
            }
            // if Active==true we want only to observe the deadend state. if active==False we are in lazy state and want to planner like there is no dead end.

            if (bPreconditionFailure)
                dsStrategy = DeadendStrategies.Active;


            return WriteTaggedDomainAndProblem(pssCurrent, lStates, dsStrategy, out cTags, out msModels);
        }
        public State WriteTaggedDomainAndProblem(CompoundFormula cfGoal, List<State> lStates, DeadendStrategies dsStrategy, out int cTags, out MemoryStream msModels)
        {
            ISet<Predicate> lObserved = new HashSet<Predicate>();
            Dictionary<string, ISet<Predicate>> dTags = GetTags(lStates, lObserved);

            cTags = dTags.Count;

            msModels = new MemoryStream();
            BinaryWriter swModels = new BinaryWriter(msModels);

            //Debug.WriteLine("Writing tagged domain");
            MemoryStream msDomain = null, msProblem = null;
            if (Options.Translation == Options.Translations.SDR)
                msDomain = Problem.Domain.WriteTaggedDomain(dTags, Problem, Problem.DeadEndList);
            else
                msDomain = Problem.Domain.WriteTaggedDomainNoState(dTags, Problem);


            msDomain.Position = 0;
            BinaryReader sr = new BinaryReader(msDomain);
            byte b = sr.ReadByte();
            while (b >= 0)
            {
                swModels.Write(b);
                if (sr.BaseStream.Position == sr.BaseStream.Length)
                {
                    break;
                }
                b = sr.ReadByte();
            }
            swModels.Write('\0');
            swModels.Flush();
            //sr.Close();




            //Debug.WriteLine("Writing tagged problem");
            if (Options.Translation == Options.Translations.SDR)
                msProblem = Problem.WriteTaggedProblem(dTags, cfGoal, lObserved, dTags.Values.First(), lStates.First().FunctionValues, dsStrategy); //the first tag is the real state
            else
                msProblem = Problem.WriteTaggedProblemNoState(dTags, lObserved, lStates.First().FunctionValues);


            msProblem.Position = 0;
            sr = new BinaryReader(msProblem);
            b = sr.ReadByte();
            while (b >= 0)
            {
                swModels.Write(b);
                if (sr.BaseStream.Position == sr.BaseStream.Length)
                {
                    break;
                }
                b = sr.ReadByte();
            }
            swModels.Write('\0');
            //sr.Close();
            swModels.Flush();



            return lStates[0];
        }



        public State WriteTaggedDomainAndProblem(PartiallySpecifiedState pssCurrent, List<State> lStates, DeadendStrategies dsStrategy, out int cTags, out MemoryStream msModels)
        {
            HashSet<Predicate> lObserved = new HashSet<Predicate>();
            Dictionary<string, ISet<Predicate>> dTags = GetTags(lStates, lObserved);

            cTags = dTags.Count;

            msModels = new MemoryStream();
            BinaryWriter swModels = new BinaryWriter(msModels);


            Domain dTagged = null;

            //Debug.WriteLine("Writing tagged domain");
            MemoryStream msDomain = null, msProblem = null;
            if (Options.Translation == Options.Translations.BestCase || Options.Translation == Options.Translations.Conformant)
                msDomain = Problem.Domain.WriteKnowledgeDomain(Problem, pssCurrent.MishapCount, pssCurrent.MinMishapCount, pssCurrent.MishapType, false);
            else if (Options.Translation == Options.Translations.SingleStateK)
                msDomain = Problem.Domain.WriteKnowledgeDomain(Problem, pssCurrent.MishapCount, pssCurrent.MinMishapCount, pssCurrent.MishapType, true);
            else if (Options.Translation == Options.Translations.SDR)
            {

                dTagged = Problem.Domain.CreateTaggedDomain(dTags, Problem, null);
                msDomain = dTagged.WriteSimpleDomain(true, false);

                /*
                Parser parser1 = new Parser();
                Domain d1 = parser1.ParseDomain(msDomain);
                
                msDomain = Problem.Domain.WriteTaggedDomain(dTags, Problem, null);

                Parser parser2 = new Parser();
                Domain d2 = parser1.ParseDomain(msDomain);
                */
            }
            else
                msDomain = Problem.Domain.WriteTaggedDomainNoState(dTags, Problem);


            msDomain.Position = 0;
            BinaryReader sr = new BinaryReader(msDomain);
            byte b = sr.ReadByte();
            while (b >= 0)
            {
                swModels.Write(b);
                if (sr.BaseStream.Position == sr.BaseStream.Length)
                {
                    break;
                }
                b = sr.ReadByte();
            }
            swModels.Write('\0');
            swModels.Flush();
            //sr.Close();





            //Debug.WriteLine("Writing tagged problem");
            if (Options.Translation == Options.Translations.BestCase || Options.Translation == Options.Translations.Conformant)
                msProblem = Problem.WriteKnowledgeProblem(new HashSet<Predicate>(pssCurrent.Observed), new HashSet<Predicate>(pssCurrent.Hidden), pssCurrent.MinMishapCount, pssCurrent.MishapCount);
            else if (Options.Translation == Options.Translations.SingleStateK)
                msProblem = Problem.WriteKnowledgeProblem(new HashSet<Predicate>(pssCurrent.Observed), new HashSet<Predicate>(lStates[0].Predicates));
            else if (Options.Translation == Options.Translations.SDR)
            {
                Problem pTagged = Problem.CreateTaggedProblem(dTagged, dTags, lObserved, dTags.Values.First(), lStates.First().FunctionValues, dsStrategy, false);
                msProblem = pTagged.WriteSimpleProblem(null);

                //Parser parser = new Parser();
                //Problem p2 = parser.ParseProblem(msProblem, dTagged);

                //msProblem = Problem.WriteTaggedProblem(dTags, lObserved, dTags.Values.First(), lStates.First().FunctionValues, dsStrategy); //the first tag is the real state
            }
            else
                msProblem = Problem.WriteTaggedProblemNoState(dTags, lObserved, lStates.First().FunctionValues);


            msProblem.Position = 0;
            sr = new BinaryReader(msProblem);
            b = sr.ReadByte();
            while (b >= 0)
            {
                swModels.Write(b);
                if (sr.BaseStream.Position == sr.BaseStream.Length)
                {
                    break;
                }
                b = sr.ReadByte();
            }
            swModels.Write('\0');
            //sr.Close();
            swModels.Flush();

            
            

            return lStates[0];
        }
        private Dictionary<string, ISet<Predicate>> GetTags(List<State> lStates, ISet<Predicate> lObserved)
        {
            Dictionary<string, ISet<Predicate>> dTags = new Dictionary<string, ISet<Predicate>>();
            int iTag = 0;
            //bugbug - what happens when there is only a single state?

            foreach (Predicate p in lStates[0].Predicates)
            {
                bool bObserved = true;
                for (int i = 1; i < lStates.Count && bObserved; i++)
                {
                    if (!lStates[i].Predicates.Contains(p))
                        bObserved = false;
                }
                if (bObserved)
                    lObserved.Add(p);
            }


            foreach (State s in lStates)
            {
                string sTag = "tag" + iTag;
                iTag++;
                ISet<Predicate> lHidden = new HashSet<Predicate>();
                foreach (Predicate p in s.Predicates)
                {
                    if (!lObserved.Contains(p))
                        lHidden.Add(p);
                }
                dTags[sTag] = lHidden;
            }
            return dTags;
        }

        private Dictionary<string, List<Predicate>> GetTags(List<List<Predicate>> lStates)
        {
            Dictionary<string, List<Predicate>> dTags = new Dictionary<string, List<Predicate>>();
            int iTag = 0;
            foreach (List<Predicate> s in lStates)
            {
                string sTag = "tag" + iTag;
                iTag++;
                /*
                foreach (Predicate p in s)
                {
                    string sPredicateName = p.ToString();
                    sPredicateName = sPredicateName.Replace("(", "");
                    sPredicateName = sPredicateName.Replace(")", "");
                    sPredicateName = sPredicateName.Replace(" ", "");
                    sTag += "_" + sPredicateName;
                }
                 */
                dTags[sTag] = s;
            }
            return dTags;
        }

        private List<ISet<Predicate>> ChooseStateSet()
        {
            if (Options.Translation == Options.Translations.BestCase || (Unknown.Count == 0 && !Problem.Domain.ContainsNonDeterministicActions))
            {
                List<ISet<Predicate>> lState = new List<ISet<Predicate>>();
                lState.Add(new HashSet<Predicate>(m_lObserved));
                return lState;
            }

            return ReviseExistingTags(Options.TagsCount);
        }

        private List<ISet<Predicate>> ChooseDeadEndState(List<Formula> lMaybeDeadends, DeadendStrategies dsStrategy, bool bPreconditionFailure)
        {
            // 1 - for each compund formula f in lMaybeDeadends add the negation of f to the hidden.
            // 2 - deadends may contradict. for the negative state, choose just one deadend.
            List<ISet<Predicate>> predicates = new List<ISet<Predicate>>();

            ISet<Predicate> lDeadendTrue = new HashSet<Predicate>();
            ISet<Predicate> lDeadendFalse = new HashSet<Predicate>();

            ISet<Predicate> lDeadendState = new HashSet<Predicate>();
            ISet<Predicate> lNoDeadendState = new HashSet<Predicate>();

            List<CompoundFormula> lHiddenNoDeadend = new List<CompoundFormula>();
            List<CompoundFormula> lHiddenDeadend = new List<CompoundFormula>();

            foreach (Formula f in lMaybeDeadends)
            {
                Formula fReduced = f.Reduce(Observed);
                if (fReduced is CompoundFormula)
                {
                    CompoundFormula cf = (CompoundFormula)fReduced;
                    lHiddenNoDeadend.Add((CompoundFormula)(cf.Negate()));
                }
                else
                {
                    PredicateFormula pf = (PredicateFormula)fReduced;
                    lDeadendFalse.Add(pf.Predicate.Negate());
                }
            }
            if (lMaybeDeadends.First() is CompoundFormula)
            {
                CompoundFormula cf = (CompoundFormula)lMaybeDeadends.First();
                if (cf.Operator == "and")
                {
                    foreach (PredicateFormula pf in cf.Operands)
                        lDeadendTrue.Add(pf.Predicate);
                }
                else
                    lHiddenDeadend.Add(cf);
            }
            else
            {
                PredicateFormula pf = (PredicateFormula)lMaybeDeadends.First();
                lDeadendTrue.Add(pf.Predicate);
            }
            lHiddenNoDeadend.AddRange(m_lHiddenFormulas);
            lHiddenDeadend.AddRange(m_lHiddenFormulas);

            lNoDeadendState = ChooseHiddenPredicatesForDeadendDetection(lHiddenNoDeadend, lDeadendFalse, bPreconditionFailure);

            lDeadendState = ChooseHiddenPredicatesForDeadendDetection(lHiddenDeadend, lDeadendTrue, bPreconditionFailure);

            m_lProblematicTag = null;

            predicates = new List<ISet<Predicate>>();

            predicates.Add(lNoDeadendState);
            predicates.Add(lDeadendState);

            return predicates;
        }
 
        private List<ISet<Predicate>> ReviseExistingTags(int cTags)
        {
            if (Options.DeadendStrategy == DeadendStrategies.Classical && m_lDeadendTags.Count > 0 && m_lProblematicTag == null)
            {
                Console.WriteLine("Deadends in B" + ID + ": " + m_lDeadendTags.Count);
                List<CompoundFormula> lHidden = new List<CompoundFormula>(m_lHiddenFormulas);
                foreach (List<Predicate> lDeadend in m_lDeadendTags)
                {
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (Predicate p in lDeadend)
                    {
                        cfOr.AddOperand(p.Negate());
                    }
                    lHidden.Add(cfOr);
                }
                HashSet<Predicate> lHiddenPredicates = new HashSet<Predicate>();
                foreach (CompoundFormula cf in lHidden)
                {
                    if (cf != null)
                    {
                        ISet<Predicate> lPredicates = cf.GetAllPredicates();
                        foreach (Predicate p in lPredicates)
                            lHiddenPredicates.Add(p.Canonical());
                    }
                }
                //RunSatSolver(lHidden, 1, null);
                ISet<Predicate> lFullAssignment = ChooseHiddenPredicates(lHidden, new HashSet<Predicate>(), lHiddenPredicates);
                if (lFullAssignment == null)
                    return null;
                m_lCurrentTags[0] = lFullAssignment;
                m_lCurrentTags[1] = m_lDeadendTags.Last();
            }
            else
            {
                if (m_lCurrentTags == null || m_lCurrentTags.Count == 0 || m_lProblematicTag == null)
                {
                    m_lCurrentTags = ChooseDiverseStateSet(cTags, null);//this is the real one!
                }
                else if (m_lProblematicTag != null)
                {
                    if (ConsistentWith(m_lCurrentTags[0]))//current tags are still valid
                    {


                        List<CompoundFormula> lHidden = new List<CompoundFormula>(m_lHiddenFormulas);
                        HashSet<Predicate> lHiddenPredicates = new HashSet<Predicate>();
                        foreach (CompoundFormula cf in lHidden)
                            if (cf != null)
                                cf.GetAllPredicates(lHiddenPredicates);
                        foreach (Predicate p in m_lProblematicTag)
                            lHiddenPredicates.Remove(p.Canonical());
                        ISet<Predicate> lFullAssignment = ChooseHiddenPredicates(lHidden, m_lProblematicTag, lHiddenPredicates);

                        List<ISet<Predicate>> lRefutationTags = new List<ISet<Predicate>>();
                        int cContinuingTags = Math.Min(m_lCurrentTags.Count, Options.TagsCount - 1);
                        if (cContinuingTags == 0)
                            cContinuingTags = 1;
                        for (int i = 0; i < cContinuingTags; i++)
                            lRefutationTags.Add(m_lCurrentTags[i]);
                        lRefutationTags.Add(lFullAssignment);
                        m_lCurrentTags = lRefutationTags;
                        /*
                        if (m_lCurrentTags.Count == cTags)
                            m_lCurrentTags[cTags - 1] = m_lProblematicTag;
                        else
                            m_lCurrentTags.Add(m_lProblematicTag);
                         * */

                    }
                    else
                    {

                        //m_lCurrentTags = RunSatSolver(m_cfCNFHiddenState, cTags - 1, m_lProblematicTag);
                        //m_lCurrentTags.Add(m_lProblematicTag);

                        m_lCurrentTags = ChooseDiverseStateSet(cTags - 1, m_lProblematicTag);
                        if (m_lCurrentTags[0].Count == 1)
                            Debug.Write("*");
                    }
                    m_lProblematicTag = null;
                }
            }



            return m_lCurrentTags;
        }

        private double DiversityLevel(List<List<Predicate>> m_lCurrentTags)
        {
            int cTags = m_lCurrentTags[0].Count;
            double cDifferent = 0;
            foreach (Predicate p in m_lCurrentTags[0])
            {
                Predicate pNegate = p.Negate();
                for (int i = 1; i < m_lCurrentTags.Count; i++)
                {
                    if (m_lCurrentTags[i].Contains(pNegate))
                    {
                        cDifferent++;
                        break;
                    }
                }
            }
            return cDifferent / cTags;
        }

        private int Choose(int k, int n)
        {
            double dNChooseKLogSpace = 0;
            int i = 0;
            for (i = 1; i <= n - k; i++)
            {
                dNChooseKLogSpace += Math.Log(k + i);
                dNChooseKLogSpace -= Math.Log(i);
            }
            double dExp = Math.Exp(dNChooseKLogSpace);
            return (int)Math.Round(dExp);
        }

        private bool ConsistentWith(ISet<Predicate> lPredicates)
        {
            /*
            CompoundFormula cfAnd = new CompoundFormula("and");
            foreach (Predicate p in lPredicates)
                cfAnd.AddOperand(p);
            return ConsistentWith(cfAnd);
             * */

            //simpler version - checking only the observed
            foreach (Predicate p in Observed)
                if (lPredicates.Contains(p.Negate()))
                    return false;
            return true;
        }


        private bool Equals(ISet<Predicate> l1, ISet<Predicate> l2)
        {
            return l1.Equals(l2);
            /*
            if (l1.Count != l2.Count)
                return false;
            foreach (Predicate p1 in l1)
                if (!Contains(l2, p1))
                    return false;
            return true;
            */
        }

        private bool Contains(ISet<Predicate> l, Predicate p)
        {
            foreach (Predicate pTag in l)
                if (p.Equals(pTag))
                    return true;
            return false;
        }

        private bool Contains(List<ISet<Predicate>> lStates, ISet<Predicate> lState)
        {
            if (lState == null)
                return true;
            foreach (ISet<Predicate> lExisting in lStates)
            {
                if (Equals(lExisting, lState))
                    return true;
            }
            return false;
        }

        private List<ISet<Predicate>> ChooseRandomStateSet(int cStates)
        {
            //List<List<Predicate>> lAssignments = RunSatSolver(m_cfCNFHiddenState, cStates);
            //return lAssignments;

            List<ISet<Predicate>> lStates = new List<ISet<Predicate>>();
            List<CompoundFormula> lConstraints = new List<CompoundFormula>(m_lHiddenFormulas);
            while (cStates > 0 || lStates.Count == 0)
            {
                ISet<Predicate> lAssignment = ChooseHiddenPredicates(lConstraints, false);

                if (!Contains(lStates, lAssignment))
                {
                    lStates.Add(lAssignment);
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (Predicate p in lAssignment)
                        cfOr.AddOperand(p.Negate());
                    lConstraints.Add(cfOr);
                }

                cStates--;
            }
            lStates = RandomPermutation(lStates);
            return lStates;

        }


 

        private List<ISet<Predicate>> ChooseDiverseStateSet(int cStates, ISet<Predicate> lCurrentTag)
        {
            List<ISet<Predicate>> lStates = new List<ISet<Predicate>>();
            if (lCurrentTag != null)
            {
                List<CompoundFormula> lHidden = new List<CompoundFormula>(m_lHiddenFormulas);
                ISet<Predicate> lToAssign = GetHiddenPredicates(lHidden);
                ISet<Predicate> lAssignment = ChooseHiddenPredicates(lHidden, lCurrentTag, lToAssign);
                lStates.Add(lAssignment);
            }
            List<CompoundFormula> lConstraints = new List<CompoundFormula>(m_lHiddenFormulas);
            if (Problem.Domain.HasNonDeterministicActions())
            {
                lConstraints.Add(Problem.Domain.GetOptionsStatement());
            }
            List<Predicate> lNotAppearing = null;
            if (lCurrentTag != null)
            {
                lNotAppearing = new List<Predicate>();
                foreach (Predicate p in lCurrentTag)
                    lNotAppearing.Add(p.Negate());
            }
            int cFailedAttempts = 0;
            int cChosenStates = 0;
            while ((cChosenStates < cStates && cFailedAttempts < cStates * 2) || lStates.Count == 0)//1 here if we want to add state negation
            {
                ISet<Predicate> lAssignment = ChooseHiddenPredicates(lConstraints, lStates, true);
                if (lNotAppearing == null)
                {
                    lNotAppearing = new List<Predicate>();
                    foreach (Predicate p in lAssignment)
                        lNotAppearing.Add(p.Negate());
                }
                else
                {
                    foreach (Predicate p in lAssignment)
                    {
                        lNotAppearing.Remove(p);
                    }
                }
                if (!Contains(lStates, lAssignment))
                {
                    lStates.Add(lAssignment);
                    /*
                    CompoundFormula cfOr = new CompoundFormula("or");
                    foreach (Predicate p in lAssignment)
                        cfOr.AddOperand(p.Negate());
                    lConstraints.Add(cfOr);
                     * */
                    cChosenStates++;
                }
                else
                    cFailedAttempts++; //here and not inside because there miFF.Search.gHt be a case where we cannot reach cStates tags
            }
            /*
            if (lNotAppearing.Count > 0)
            {
                foreach (Predicate p in lStates.Last())
                {
                    if (!lNotAppearing.Contains(p.Negate()))
                        lNotAppearing.Add(p);
                }
                lStates.Add(lNotAppearing);
            }
            */
            //lStates = RandomPermutation(lStates);
            return lStates;

        }

        private ISet<Predicate> GetNonAppearingPredicates(List<ISet<Predicate>> lChosen)
        {
            ISet<Predicate> lNotAppearing = new HashSet<Predicate>();
            foreach (Predicate p in lChosen[0])
                lNotAppearing.Add(p.Negate());

            for (int i = 1; i < lChosen.Count; i++)
            {
                foreach (Predicate p in lChosen[i])
                {
                    lNotAppearing.Remove(p);
                }
            }
            return lNotAppearing;
        }

        private List<ISet<Predicate>> RandomPermutation(List<ISet<Predicate>> lStates)
        {
            List<ISet<Predicate>> lPermuted = new List<ISet<Predicate>>();
            while (lStates.Count > 1)
            {
                int idx = RandomGenerator.Next(lStates.Count);
                lPermuted.Add(lStates[idx]);
                lStates.RemoveAt(idx);
            }
            lPermuted.Add(lStates[0]);
            return lPermuted;
        }

        public ISet<Predicate> RunSatSolver()
        {
            List<Formula> lFormulas = new List<Formula>(m_lHiddenFormulas);
            List<ISet<Predicate>> l = RunSatSolver(lFormulas, 1, null);
            return l[0];
        }

        public List<ISet<Predicate>> RunSatSolver(List<Formula> lFormulas, int cAttempts)
        {
            return RunSatSolver(lFormulas, cAttempts, null);
        }

        private string m_sFFOutput;
        private void OutputHandler(object sendingProcess, DataReceivedEventArgs outLine)
        {
            m_sFFOutput += outLine.Data + "\n";
        }

        TimeSpan tsTotalRunSatSolver = new TimeSpan();
        TimeSpan tsTotalRunMiniSat = new TimeSpan();
        long cRuns = 0, iSize = 0;



        public bool ApplyUnitPropogation(List<Formula> lFormulas, HashSet<Predicate> lAssignment)
        {
            DateTime dtStart = DateTime.Now;
            List<PredicateFormula> lNewlyLearnedPredicates = new List<PredicateFormula>();
            List<PredicateFormula> lAllLearnedPredicates = new List<PredicateFormula>();
            for (int iFormula = 0; iFormula < lFormulas.Count; iFormula++)
            {
                Formula f = lFormulas[iFormula];
                if (f is PredicateFormula)
                {
                    lNewlyLearnedPredicates.Add((PredicateFormula)f);
                    lAllLearnedPredicates.Add((PredicateFormula)f);
                    lFormulas[iFormula] = null;
                }
            }
            int cIndexes = 0, cValidIndexes = 0, cLearned = 0;
            DateTime dt1 = DateTime.Now;
            TimeSpan ts1 = new TimeSpan(0), ts2 = new TimeSpan(0), ts3 = new TimeSpan(0);


            int cReductions = 0;
            while (lNewlyLearnedPredicates.Count > 0)
            {
                HashSet<int> lIndexes = new HashSet<int>();
                ISet<Predicate> lKnown = new HashSet<Predicate>();
                foreach (PredicateFormula pf in lNewlyLearnedPredicates)
                {
                    GroundedPredicate p = (GroundedPredicate)pf.Predicate.Canonical();
                    lKnown.Add(pf.Predicate);
                    lAssignment.Add(pf.Predicate);
                    if (m_dMapPredicatesToFormulas.ContainsKey(p))
                    {
                        List<int> lRelevantFormulas = m_dMapPredicatesToFormulas[p];
                        foreach (int idx in lRelevantFormulas)
                            lIndexes.Add(idx);
                    }
                    else if (p.Name == Utilities.OPTION_PREDICATE)
                    {
                        for (int i = 0; i < lFormulas.Count; i++)
                            lIndexes.Add(i);
                    }
                }
                DateTime dt2 = DateTime.Now;
                ts1 += dt2 - dt1;
                dt1 = dt2;
                lNewlyLearnedPredicates = new List<PredicateFormula>();
                foreach (int idx in lIndexes)
                {
                    cIndexes++;
                    CompoundFormula cfPrevious = (CompoundFormula)lFormulas[idx];
                    if (cfPrevious != null)
                    {
                        cValidIndexes++;

                        DateTime dt3 = DateTime.Now;
                        Formula fNew = cfPrevious.Reduce(lKnown);
                        cReductions++;
                        ts2 += DateTime.Now - dt3;

                        if (fNew.IsFalse(null))
                            return false;

                        if (fNew is PredicateFormula)
                        {
                            if (!fNew.IsTrue(null))
                            {
                                if (lAllLearnedPredicates.Contains(fNew.Negate()))
                                    return false;
                                lNewlyLearnedPredicates.Add((PredicateFormula)fNew);
                                lAllLearnedPredicates.Add((PredicateFormula)fNew);
                            }
                            lFormulas[idx] = null;
                        }
                        else
                        {
                            CompoundFormula cfNew = (CompoundFormula)fNew;
                            if (cfNew.IsSimpleConjunction())
                            {
                                foreach (PredicateFormula pf in cfNew.Operands)
                                {
                                    if (!fNew.IsTrue(null))
                                    {
                                        if (lAllLearnedPredicates.Contains(pf.Negate()))
                                            return false;
                                        lNewlyLearnedPredicates.Add(pf);
                                        lAllLearnedPredicates.Add(pf);
                                    }
                                }
                                lFormulas[idx] = null;
                            }
                            else
                                lFormulas[idx] = fNew;
                        }
                    }
                }
                dt2 = DateTime.Now;
                ts3 += dt2 - dt1;
                dt1 = dt2;

            }

            TimeSpan tsCurrent = DateTime.Now - dtStart;
            tsTotalTime += tsCurrent;
            //Debug.WriteLine("ApplyUnitPropogation: indexes " + cIndexes + ", valid " + cValidIndexes + ", learned " + cLearned + " time " + tsCurrent.TotalSeconds);
            //Debug.WriteLine(cReductions + ", " + ts1.TotalSeconds + ", " + ts2.TotalSeconds + ", " + ts3.TotalSeconds);
            return true;
        }

        public List<ISet<Predicate>> RunSatSolver(List<Formula> lFormulas, int cAttempts, ISet<Predicate> lProblematicTag)
        {
            HashSet<Predicate> lPartialAssignment = new HashSet<Predicate>();


            if (!ApplyUnitPropogation(lFormulas, lPartialAssignment))
                return new List<ISet<Predicate>>();
            bool bAllNull = true;


            if (cAttempts > 1)
                Debug.WriteLine("*");

            DateTime dtStart = DateTime.Now;
            List<ISet<Predicate>> lAssignments = new List<ISet<Predicate>>();

            foreach (Formula f in lFormulas)
                if (f != null)
                    bAllNull = false;
            if (bAllNull)//solved by unit propogation
            {
                lAssignments.Add(new HashSet<Predicate>(lPartialAssignment));
                return lAssignments;
            }



            ISet<Predicate> lAssignment = lProblematicTag;

            if (lAssignment != null)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                foreach (Predicate pAssigned in lAssignment)
                    cfOr.AddOperand(pAssigned.Negate());
                lFormulas.Add(cfOr);
            }

            List<List<int>> lIntCluases = GetCNFClauses(lFormulas);
            HashSet<int> lParticipatingVariables = new HashSet<int>();
            foreach (List<int> lClause in lIntCluases)
            {
                foreach (int i in lClause)
                {
                    if (i != 0)
                        lParticipatingVariables.Add(Math.Abs(i));
                }
            }



            ConstraintSystem solver = ConstraintSystem.CreateSolver();
            Dictionary<int, CspTerm> dVariables = new Dictionary<int, CspTerm>();
            foreach (int idx in lParticipatingVariables)
                dVariables[idx] = solver.CreateBoolean("v" + idx);
            foreach (List<int> lClause in lIntCluases)
            {
                List<CspTerm> lTerms = new List<CspTerm>();
                foreach (int v in lClause)
                {
                    int idx = Math.Abs(v);
                    if (idx != 0)
                    {
                        CspTerm var = dVariables[idx];
                        if (v > 0)
                            lTerms.Add(var);
                        else
                            lTerms.Add(solver.Not(var));
                    }

                }
                CspTerm tOr = solver.Or(lTerms.ToArray());
                solver.AddConstraints(tOr);
            }
            ConstraintSolverSolution solution = solver.Solve();

            if (solution.HasFoundSolution)
            {
                ISet<Predicate> lSolution = new HashSet<Predicate>();

                foreach (KeyValuePair<int, CspTerm> p in dVariables)
                {
                    int idx = p.Key - 1;
                    if (idx < Problem.GetSATVariablesCount())
                    {
                        Predicate pAssigned = Problem.GetPredicateByIndex(idx);
                        int value = (int)solution[p.Value];
                        if (value == 0)
                            lSolution.Add(pAssigned.Negate());
                        else
                            lSolution.Add(pAssigned);
                    }
                }



                lAssignments.Add(lSolution);
            }
            tsTotalRunSatSolver += DateTime.Now - dtStart;
            cRuns++;


            return lAssignments;
        }



        private List<List<int>> GetCNFClauses(List<Formula> lFormulas)
        {

            List<List<int>> lIntCluases = new List<List<int>>();

            foreach (Formula f in lFormulas)
            {
                if (f == null)
                    continue;
                if (f is PredicateFormula)
                {
                    Predicate p = ((PredicateFormula)f).Predicate;
                    List<int> lClause = new List<int>();
                    int idx = Problem.GetPredicateIndex(p);
                    if (p.Negation)
                        idx *= -1;
                    lClause.Add(idx);
                    lClause.Add(0);
                    lIntCluases.Add(lClause);
                }
                else
                {
                    CompoundFormula cf = (CompoundFormula)f;

                    if (cf.SATSolverClauses.Count == 0)
                    {
                        if (cf.Operator == "or")
                        {
                            List<int> lClause = new List<int>();
                            foreach (PredicateFormula pf in cf.Operands)
                            {
                                Predicate p = pf.Predicate;
                                int idx = Problem.GetPredicateIndex(p);
                                if (p.Negation)
                                    idx *= -1;
                                lClause.Add(idx);
                            }
                            lClause.Add(0);
                            cf.AddSATSolverClause(lClause);
                        }
                        else if (cf.Operator == "oneof")
                        {
                            //using a simple conversion here - (oneof p1 p2 p3) = (and (or ~p1 ~p2) (or ~p1 ~p3) (or ~p2 ~p3) (or p1 p2 p3))
                            List<int> lClause = null;
                            if (cf.IsSimpleOneOf())
                            {
                                List<Predicate> lPredicates = new List<Predicate>(cf.GetAllPredicates());
                                for (int i = 0; i < lPredicates.Count - 1; i++)
                                {
                                    int idx1 = Problem.GetPredicateIndex(lPredicates[i]);
                                    if (!lPredicates[i].Negation)
                                        idx1 *= -1;
                                    for (int j = i + 1; j < lPredicates.Count; j++)
                                    {
                                        int idx2 = Problem.GetPredicateIndex(lPredicates[j]);
                                        if (!lPredicates[j].Negation)
                                            idx2 *= -1;
                                        lClause = new List<int>();
                                        lClause.Add(idx1);
                                        lClause.Add(idx2);
                                        lClause.Add(0);
                                        cf.AddSATSolverClause(lClause);
                                    }
                                }
                                lClause = new List<int>();
                                foreach (Predicate p in lPredicates)
                                {
                                    int idx = Problem.GetPredicateIndex(p);
                                    if (p.Negation)
                                        idx *= -1;
                                    lClause.Add(idx);
                                }
                                lClause.Add(0);
                                cf.AddSATSolverClause(lClause);
                            }
                            else
                            {
                                //using a simple conversion here - (oneof p1 (or p2 p3)) = (and (or ~p1 ~p2) (or ~p1 ~p3) (or p1 p2 p3))
                                int cOperands = cf.Operands.Count;
                                CompoundFormula cfOrAll = new CompoundFormula("or");
                                HashSet<int> hsAll = new HashSet<int>();
                                for (int i = 0; i < cOperands; i++)
                                {
                                    if (cf.Operands[i] is PredicateFormula || ((CompoundFormula)(cf.Operands[i])).IsSimpleDisjunction())
                                    {
                                        ISet<Predicate> lFirstPredicates = cf.Operands[i].GetAllPredicates();
                                        for (int j = i + 1; j < cOperands; j++)
                                        {
                                            ISet<Predicate> lSecondPredicates = cf.Operands[j].GetAllPredicates();
                                            foreach (Predicate pFirst in lFirstPredicates)
                                            {
                                                int idx1 = Problem.GetPredicateIndex(pFirst);
                                                if (pFirst.Negation)
                                                    hsAll.Add(idx1 * -1);
                                                else
                                                {
                                                    hsAll.Add(idx1);
                                                    idx1 *= -1;
                                                }
                                                foreach (Predicate pSecond in lSecondPredicates)
                                                {
                                                    int idx2 = Problem.GetPredicateIndex(pSecond);
                                                    if (pSecond.Negation)
                                                        hsAll.Add(idx2 * -1);
                                                    else
                                                    {
                                                        hsAll.Add(idx2);
                                                        idx2 *= -1;
                                                    }
                                                    lClause = new List<int>();
                                                    lClause.Add(idx1);
                                                    lClause.Add(idx2);
                                                    lClause.Add(0);
                                                    cf.AddSATSolverClause(lClause);
                                                }
                                            }
                                        }
                                    }
                                    else //not handling the case of neting "and" for now
                                        throw new NotImplementedException();
                                }
                                lClause = new List<int>();
                                foreach (int i in hsAll)
                                    lClause.Add(i);
                                lClause.Add(0);
                                cf.AddSATSolverClause(lClause);
                            }
                        }
                        else
                            throw new NotImplementedException();
                    }
                    lIntCluases.AddRange(cf.SATSolverClauses);
                }
            }
#if DEBUG
            /*StreamWriter swDebug = null;
            swDebug = new StreamWriter(Problem.Domain.Path + "problem.sat.debug");
            foreach (Formula f in lFormulas)
                swDebug.WriteLine(f);
            swDebug.Close();*/
#endif


            return lIntCluases;
        }



        private MemoryStream WriteCNF(List<Formula> lFormulas)
        {


            List<List<int>> lIntCluases = GetCNFClauses(lFormulas);
            MemoryStream ms = new MemoryStream();

            StreamWriter sw = new StreamWriter(ms);
            sw.WriteLine("p cnf " + Problem.GetSATVariablesCount() + " " + lIntCluases.Count);
            foreach (List<int> lClause in lIntCluases)
            {
                foreach (int i in lClause)
                    sw.Write(i + " ");
                sw.WriteLine();
            }

            sw.Flush();

            MemoryStream ms2 = new MemoryStream();
            ms.Position = 0;
            BinaryReader br = new BinaryReader(ms);
            BinaryWriter bw = new BinaryWriter(ms2);
            byte b = br.ReadByte();
            while (b >= 0)
            {
                bw.Write(b);
                if (br.BaseStream.Position == br.BaseStream.Length)
                {
                    break;
                }
                b = br.ReadByte();
            }
            bw.Write('\0');
            bw.Flush();
            //sw.Close();
            return ms2;
        }

        private HashSet<int> WriteCNF(List<Formula> lFormulas, StreamWriter sw)
        {
            List<List<int>> lIntCluases = GetCNFClauses(lFormulas);
            HashSet<int> lParticipatingVariables = new HashSet<int>();
            //MemoryStream ms = new MemoryStream();

            sw.WriteLine("p cnf " + Problem.GetSATVariablesCount() + " " + lIntCluases.Count);
            foreach (List<int> lClause in lIntCluases)
            {
                string s = "";
                foreach (int i in lClause)
                {
                    if (i != 0)
                        lParticipatingVariables.Add(Math.Abs(i));
                    s += i + " ";
                }
                sw.WriteLine(s);
                iSize += s.Length;
            }
            /*
            StringBuilder sb = new StringBuilder();
            //StringWriter sw1 = new StringWriter(sb);
            //sw1.WriteLine("p cnf " + m_dSATVariables.Count + " " + lIntCluases.Count);
            sb.Append("p cnf " + m_dSATVariables.Count + " " + lIntCluases.Count + "\n");
            foreach (List<int> lClause in lIntCluases)
            {
                string s = "";
                foreach (int i in lClause)
                    s += i + " ";
                //sw1.WriteLine(s);
                sb.Append(s + "\n");
                iSize += s.Length;
            }
             sw.WriteLine(sb.ToString());
           */
            //sw.Write(0);
            sw.Flush();
            return lParticipatingVariables;
        }

        private int CopyToCharArray(char[] a, int iStart, string s)
        {
            for (int i = 0; i < s.Length; i++)
            {
                a[iStart + i] = s[i];
            }
            return iStart + s.Length;
        }
        private char[] GetCNF(List<Formula> lFormulas)
        {
            List<List<int>> lIntCluases = GetCNFClauses(lFormulas);
            int cChars = 0;
            foreach (List<int> lClause in lIntCluases)
            {
                cChars += lClause.Count;
            }
            char[] aChars = new char[cChars * 10];
            int iCurrentChar = 0;
            iCurrentChar = CopyToCharArray(aChars, iCurrentChar, "p cnf " + Problem.GetSATVariablesCount() + " " + lIntCluases.Count);
            foreach (List<int> lClause in lIntCluases)
            {
                string s = "";
                foreach (int i in lClause)
                    s += i + " ";
                iCurrentChar = CopyToCharArray(aChars, iCurrentChar, s);
                iSize += s.Length;
            }
            /*
            StringBuilder sb = new StringBuilder();
            //StringWriter sw1 = new StringWriter(sb);
            //sw1.WriteLine("p cnf " + m_dSATVariables.Count + " " + lIntCluases.Count);
            sb.Append("p cnf " + m_dSATVariables.Count + " " + lIntCluases.Count + "\n");
            foreach (List<int> lClause in lIntCluases)
            {
                string s = "";
                foreach (int i in lClause)
                    s += i + " ";
                //sw1.WriteLine(s);
                sb.Append(s + "\n");
                iSize += s.Length;
            }
             sw.WriteLine(sb.ToString());
           */
            aChars[iCurrentChar] = (char)0;
            return aChars;
        }

        public PartiallySpecifiedState GetPartiallySpecifiedState()
        {
            PartiallySpecifiedState pss = new PartiallySpecifiedState(this);
            if (Options.EnforceCNF)
                m_cfCNFHiddenState = (CompoundFormula)m_cfCNFHiddenState.ToCNF();
            return pss;
        }

        /*
        private CompoundFormula ToCNF(List<CompoundFormula> lHidden)
        {
            CompoundFormula cfAnd = new CompoundFormula("and");
            foreach (CompoundFormula cfHidden in lHidden)
            {
                cfAnd.AddOperand(cfHidden);
            }
            CompoundFormula cfCNF = cfAnd.ToCNF();
            return cfAnd;
        }
         * */

        public bool ConsistentWith(Predicate p)
        {

            ISet<Predicate> lKnown = new HashSet<Predicate>(Observed);
            lKnown.Add(p);
            Formula fReduced = m_cfCNFHiddenState.Reduce(lKnown);
            if (fReduced.IsFalse(lKnown))
                return false;
            return true;
            /*
            List<Predicate> lKnown = new List<Predicate>();
            lKnown.Add(p);
            if (m_cfCNFHiddenState.IsFalse(lKnown))
                return false;
            return true;*/
        }

        int count_revisions = 0;
        public HashSet<int> ReviseInitialBelief(Formula fObserve, PartiallySpecifiedState pssLast)
        {
            
            DateTime dtBefore = DateTime.Now;
            CPORStack<PartiallySpecifiedState> sTrace = new CPORStack<PartiallySpecifiedState>();
            CPORStack<List<Formula>> sForumalsTrace = new CPORStack<List<Formula>>();
            PartiallySpecifiedState pssCurrent = pssLast, pssSuccessor = null;
            HashSet<int> hsModifiedClauses = new HashSet<int>();
            //Formula fToRegress = fObserve, fRegressed = null;
            bool bTrueRegression = false;
            int cSteps = 0;

            count_revisions++;
            List<Formula> lCurrentFormulas = new List<Formula>();
            List<Formula> lRegressedFormulas = new List<Formula>();

            lCurrentFormulas.Add(fObserve);

            //TimeSpan ts1 = new TimeSpan(0), ts2 = new TimeSpan(0);
            //DateTime dtStart = DateTime.Now;
            if (pssCurrent.Predecessor == null)
                sTrace.Push(pssCurrent);
            while (pssCurrent.Predecessor != null)
            {
                sTrace.Push(pssCurrent);
                sForumalsTrace.Push(lCurrentFormulas);
                lRegressedFormulas = new List<Formula>();
                HashSet<Predicate> hsNew = new HashSet<Predicate>();
                foreach (Formula fCurrent in lCurrentFormulas)
                {
                    if (fCurrent.IsTrue(pssCurrent.Observed))
                        continue;//used to be break but I think that if we got here then there is no point in continuing...
                    //is false doesn't properly work here
                    //Debug.Assert(fCurrent.IsFalse(pssCurrent.Observed), "Rgression of an observation returned false");
                    //pssCurrent.GeneratingAction.ClearConditionsChoices();
                    //pssCurrent.GeneratingAction.RemoveImpossibleOptions(pssCurrent.Observed); Need to this after the regression (below)
                    //DateTime dt = DateTime.Now;
                    Formula fRegressed = pssCurrent.RegressObservation(fCurrent);
                    //ts1 += DateTime.Now - dt;
                    if (fRegressed is CompoundFormula)
                    {
                        CompoundFormula cf = (CompoundFormula)fRegressed;
                        if (cf.Operator != "and")
                            lRegressedFormulas.Add(fRegressed);
                        else
                            foreach (Formula f in cf.Operands)
                                lRegressedFormulas.Add(f);

                    }
                    else
                        lRegressedFormulas.Add(fRegressed);

                    //dt = DateTime.Now;
                    //must be after the regression so as not to make everything already known
                    //we are not propgating the things that we learn if we are in offline mode
                    if (!Options.OptimizeMemoryConsumption && !Options.ComputeCompletePlanTree)
                        hsNew.UnionWith(pssCurrent.AddObserved(fCurrent));
                    //ts2 += DateTime.Now - dt;
                    //pssCurrent.AddObserved(fToRegress); //Not sure that this is valid!

                    if (!fRegressed.Equals(fCurrent))
                        //if (bTrueRegression || !fRegressed.Equals(fToRegress))
                        bTrueRegression = true;
                }
                if (hsNew.Count > 0 && pssSuccessor != null)
                    pssSuccessor.PropogateObservedPredicates(hsNew);
                pssSuccessor = pssCurrent;
                pssCurrent = pssCurrent.Predecessor;
                cSteps++;
                lCurrentFormulas = lRegressedFormulas;
            }

            Formula fFinal = null;
            if (lCurrentFormulas.Count == 0)
                return hsModifiedClauses;
            if (lCurrentFormulas.Count == 1)
                fFinal = lCurrentFormulas[0].Reduce(Observed);
            else
            {
                CompoundFormula cf = new CompoundFormula("and");
                foreach (Formula f in lCurrentFormulas)
                {
                    Formula fReduced = f.Reduce(Observed).Simplify();
                    Formula fCNF = null;
                    if (fReduced is CompoundFormula)
                        fCNF = ((CompoundFormula)fReduced).ToCNF();
                    else
                        fCNF = fReduced;
                    cf.AddOperand(fCNF);
                }
                fFinal = cf;

            }
            //Debug.WriteLine("Total time in regressobs " + ts1.TotalSeconds + " propogate " + ts2.TotalSeconds +
            //     " all " + (DateTime.Now - dtStart).TotalSeconds + " size " + fFinal.Size);

            if (fFinal.IsTrue(null))
                return hsModifiedClauses;
            DateTime dtAfterRegression = DateTime.Now;

            DateTime dtAfterReasoning = DateTime.Now;
            //Seems likely but I am unsure: if there was no real regression, then learned things can be applied to all states as is

            HashSet<Predicate> lLearned = null;
            if (BeliefState.UseEfficientFormulas)
                lLearned = AddReasoningFormulaEfficient(fFinal);
            else
                lLearned = AddReasoningFormula(fFinal, hsModifiedClauses);

            if (lLearned.Count > 0)
            {
                //HashSet<Predicate> lLearned = pssCurrent.ApplyReasoning(); not needed since we got the learned predicates from the belief update
                if (!Options.ComputeCompletePlanTree)
                    pssCurrent.AddObserved(lLearned);
                dtAfterReasoning = DateTime.Now;
                if (bTrueRegression)
                {
                    //commenting out the condition below - PropogateObservedPredicates already takes all this into consideration
                    /*
                    if ((Options.OptimizeMemoryConsumption || Options.ComputeCompletePlanTree) && lLearned.Count > 0)
                    {
                        
                        pssLast.AddObserved(lLearned);
                    }
                    else
                    */
                    {
                        while (sTrace.Count > 0 && lLearned.Count > 0)
                        {
                            pssCurrent = sTrace.Pop();
                            //bUpdate = pssCurrent.PropogateObservedPredicates();
                            lLearned = pssCurrent.PropogateObservedPredicates(lLearned);
                        }
                    }
                }
                else
                {
                    if (!Options.OptimizeMemoryConsumption && !Options.ComputeCompletePlanTree)
                    {
                        while (sTrace.Count > 0)
                        {
                            pssCurrent = sTrace.Pop();
                            pssCurrent.AddObserved(lLearned);
                        }
                    }
                    else
                        pssLast.AddObserved(lLearned);
                }

            }
            /*
            Debug.WriteLine("Time for belief update: " +
                (DateTime.Now - dtBefore).TotalSeconds +
                " regression " + (dtAfterRegression - dtBefore).TotalSeconds +
                " reasoning " + (dtAfterReasoning - dtAfterRegression).TotalSeconds +
                " update " + (DateTime.Now - dtAfterReasoning).TotalSeconds);
            */


            return hsModifiedClauses;
        }
        public State WriteHiddenState(string sFileName, bool bWriteObserved)
        {
            State s = ChooseState(false);
            StreamWriter sw = new StreamWriter(sFileName);
            foreach (GroundedPredicate gp in s.Predicates)
            {
                if (bWriteObserved || !Observed.Contains(gp))
                {
                    Predicate p = gp;
                    if (gp.Negation)
                        p = gp.Negate();
                    string sName = p.ToString().Replace(" ", "_").Replace("(", "").Replace(")", "").ToUpper();
                    if (gp.Negation)
                        sName = "KN_" + sName;
                    else
                        sName = "K_" + sName;
                    sw.WriteLine(sName);
                }
            }
            sw.Close();
            return s;
        }


        public void AddCurrentToDeadendTags()
        {
            if (m_lCurrentTags.Count > 0)
            {
                foreach (ISet<Predicate> lDeadend in m_lDeadendTags)
                {
                    if (SameElements(lDeadend, m_lCurrentTags[0]))
                        return;
                }
                m_lDeadendTags.Add(m_lCurrentTags[0]);
            }
        }

        private bool SameElements(ISet<Predicate> l1, ISet<Predicate> l2)
        {
            if (l1.Count != l2.Count)
                return false;
            foreach (Predicate p in l1)
                if (!l2.Contains(p))
                    return false;
            return true;
        }

        public void SetProblematicTagToCurrent()
        {
            if (m_lCurrentTags.Count > 0)
            {
                m_lProblematicTag = m_lCurrentTags[0];
            }
        }

    }
}
