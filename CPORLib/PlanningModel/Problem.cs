using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.Tools;

namespace CPORLib.PlanningModel
{
    public class Problem
    {

        public string Name { get; private set; }
        public Formula Goal { get; set; }
        public Domain Domain { get; private set; }
        private HashSet<Predicate> m_lKnown;
        private List<CompoundFormula> m_lHidden;
        public IEnumerable<CompoundFormula> Hidden { get { return m_lHidden; } }
        public ISet<Predicate> Known { get { return m_lKnown; } }
        public ISet<Predicate> Unknown { get { return m_lInitiallyUnknown; } }
        public List<PlanningAction> ReasoningActions { get; private set; }
        public string MetricStatement { get; private set; }
        private HashSet<Predicate> m_lInitiallyUnknown;


        private Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> m_dRelevantPredicates;

        public List<Formula> DeadEndList { get; set; }

        public Problem(string sName, Domain d)
        {
            Domain = d;
            m_lKnown = new HashSet<Predicate>();
            m_lHidden = new List<CompoundFormula>();
            Name = sName;
            Goal = null;
            ReasoningActions = new List<PlanningAction>();
            m_dRelevantPredicates = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            m_lInitiallyUnknown = new HashSet<Predicate>();
            DeadEndList = new List<Formula>();
        }

        public void AddKnown(Predicate p)
        {
            m_lKnown.Add(p);
        }
        public void RemoveKnown(Predicate p)
        {
            m_lKnown.Remove(p);
        }
        public bool InitiallyUnknown(Predicate p)
        {
            return m_lInitiallyUnknown.Contains(p.Canonical());
        }
        public void AddHidden(CompoundFormula cf)
        {
            Domain.AddHidden(cf);

            ISet<Predicate> hs = cf.GetAllPredicates();
            foreach (GroundedPredicate gp in hs)
            {
                m_lInitiallyUnknown.Add(gp.Canonical());
                GroundedPredicate gpCanonical = (GroundedPredicate)gp.Canonical();
                if (!m_dRelevantPredicates.ContainsKey(gpCanonical))
                    m_dRelevantPredicates[gpCanonical] = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate gpOther in hs)
                {
                    GroundedPredicate gpOtherCanonical = (GroundedPredicate)gpOther.Canonical();
                    if (gpOtherCanonical != gpCanonical)
                        m_dRelevantPredicates[gpCanonical].Add(gpOtherCanonical);
                }

            }

            m_lHidden.Add(cf);
        }
        public override string ToString()
        {
            string s = "(problem " + Name + "\n";
            s += "(domain " + Domain.Name + ")\n";
            s += "(init \n";
            s += "(known";
            foreach (Predicate p in m_lKnown)
                s += " " + p;
            s+= ")\n";
            
            s += "(hidden " + Utilities.ListToString(m_lHidden) + ")\n)\n";
            s+= "(goal " + Goal + ")\n";
            s += ")";
            return s;
        }

        public void CompleteKnownState()
        {
            List<string> lKnownPredicates = new List<string>();
            foreach (Predicate p in m_lKnown)
                if (!lKnownPredicates.Contains(p.Name))
                    lKnownPredicates.Add(p.Name);
            // List<GroundedPredicate> lGrounded = Domain.GroundAllPredicates(lKnownPredicates);
            ISet<Predicate> lGrounded = Domain.GroundAllPredicates();
            ISet<Predicate> lUnknown = new HashSet<Predicate>();
            foreach (Formula f in m_lHidden)
                f.GetAllPredicates(lUnknown);
            foreach (GroundedPredicate gp in lGrounded)
            {
                if (!(Domain.AlwaysConstant(gp) && Domain.AlwaysKnown(gp))) //not sure why I thouhgt that constant predicates do not apply here. We need them for planning in K domain.
                {
                    if (lUnknown.Contains(gp) || lUnknown.Contains(gp.Negate()) || m_lKnown.Contains(gp) || m_lKnown.Contains(gp.Negate()))
                    {
                        //do nothing
                    }
                    else
                    {

                        m_lKnown.Add(gp.Negate());
                    }
                }
            }
        }

        public void AddReasoningActions()
        {
            ReasoningActions = new List<PlanningAction>();
            foreach (CompoundFormula cf in m_lHidden)
            {
                if (cf.Operator == "oneof")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        if (cf.Operands.Count > 2)
                        {
                            CompoundFormula cfNegativeEffects = new CompoundFormula("and");
                            CompoundFormula cfPositiveEffects = new CompoundFormula("or");
                            foreach (Formula fOther in cf.Operands)
                            {
                                if (!fOther.Equals(f))
                                {
                                    cfNegativeEffects.AddOperand(f.Negate());
                                }
                                AddReasoningAction(f, cfNegativeEffects);
                            }
                        }
                        else
                        {
                            AddReasoningAction(cf.Operands[0], cf.Operands[1].Negate());
                            AddReasoningAction(cf.Operands[1], cf.Operands[0].Negate());
                        }
                    }
                }
                else
                    throw new NotImplementedException("Not implementing or for now");
            }
        }

        private void AddReasoningAction(Formula fPreconditions, Formula fEffect)
        {
            PlanningAction a = new PlanningAction("Reasoning" + ReasoningActions.Count);
            a.Preconditions = fPreconditions;
            a.SetEffects(fEffect);
            ReasoningActions.Add(a);
        }

        public BeliefState GetInitialBelief()
        {
            Debug.WriteLine("Generating initial belief state");
            BeliefState bs = new BeliefState(this);
            foreach (GroundedPredicate p in m_lKnown)
            {
                if (p.Name == "=")
                {
                    bs.FunctionValues[p.Constants[0].Name] = double.Parse(p.Constants[1].Name);
                }
                else
                    bs.AddObserved(p);
            }
            foreach (CompoundFormula cf in m_lHidden)
            {
                /*
                Formula fReduced = cf.Reduce(m_lKnown);
                if (fReduced is CompoundFormula)
                    bs.AddInitialStateFormula(((CompoundFormula)fReduced));
                */
                bs.AddInitialStateFormula(cf);

            }
            //bs.InitDNF();
            return bs;
        }

        public bool IsGoalState(State s)
        {
            return s.Contains(Goal);
        }

        public void WriteReasoningActions(StreamWriter sw, bool bRequireP)
        {
            int cActions = 0;
            foreach (CompoundFormula cfHidden in m_lHidden)
            {
                cActions = WriteReasoningActions(sw, cfHidden, cActions, bRequireP);
            }
        }




        public void WriteReasoningAxioms(StreamWriter sw)
        {
            int cActions = 0;
            foreach (CompoundFormula cfHidden in m_lHidden)
            {
                cActions = WriteReasoningAxioms(sw, cfHidden, cActions);
            }
        }

        private void WriteResoningAction(StreamWriter sw, HashSet<Predicate> lPreconditions, HashSet<Predicate> lEffects, int iNumber)
        {
            sw.WriteLine("(:action R" + iNumber);
            sw.Write(":precondition (and");
            foreach (Predicate pPrecondition in lPreconditions)
            {
                sw.Write(pPrecondition);
            }
            sw.WriteLine(")");
            sw.Write(":effect (and");
            foreach (Predicate pEffect in lEffects)
            {
                sw.Write(pEffect);
            }
            sw.WriteLine(")");
            sw.WriteLine(")");
        }

        private void WriteResoningAxiom(StreamWriter sw, HashSet<Predicate> lPreconditions, HashSet<Predicate> lEffects, int iNumber)
        {
            sw.WriteLine("(:axiom");
            sw.Write(":context (and");
            foreach (Predicate pPrecondition in lPreconditions)
            {
                sw.Write(pPrecondition);
            }
            sw.WriteLine(")");
            sw.Write(":implies (and");
            foreach (Predicate pEffect in lEffects)
            {
                sw.Write(pEffect);
            }
            sw.WriteLine(")");
            sw.WriteLine(")");
        }

        private void AddReasoningAction(HashSet<Predicate> lPreconditions, HashSet<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            List<Predicate> lKnowPreconditions = new List<Predicate>();
            foreach (GroundedPredicate p in lPreconditions)
            {
                Predicate pKnow = Predicate.GenerateKnowPredicate(p);
                lKnowPreconditions.Add(pKnow);
                lKnowPreconditions.Add(p);
            }
            List<Predicate> lKnowEffects = new List<Predicate>();
            foreach (GroundedPredicate p in lEffects)
            {
                Predicate pKnow = Predicate.GenerateKnowPredicate(p);
                lKnowEffects.Add(pKnow);
            }
            if (dActions.ContainsKey(lKnowPreconditions))
            {
                if (dActions.Comparer.Equals(lKnowEffects, dActions[lKnowPreconditions]))
                    return;
                throw new NotImplementedException();
            }
            dActions[lKnowPreconditions] = lKnowEffects;
        }

        private void AddReasoningAction(List<GroundedPredicate> lAssignment, List<Predicate> lKnown, List<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            List<Predicate> lPreconditions = new List<Predicate>(lAssignment);
            lPreconditions.AddRange(lKnown);

            List<Predicate> lKnowEffects = new List<Predicate>();
            foreach (GroundedPredicate p in lEffects)
            {
                Predicate pKnow = Predicate.GenerateKnowPredicate(p);
                lKnowEffects.Add(pKnow);
            }
            if (dActions.ContainsKey(lPreconditions))
            {
                if (dActions.Comparer.Equals(lKnowEffects, dActions[lPreconditions]))
                    return;
                throw new NotImplementedException();
            }
            dActions[lPreconditions] = lKnowEffects;
        }

        private void AddReasoningActions(Formula fUnknown, HashSet<Predicate> lUnassigned, HashSet<Predicate> lAssigned, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            if (fUnknown is PredicateFormula)
            {
                HashSet<Predicate> lEffects = new HashSet<Predicate>();
                Predicate pEffect = ((PredicateFormula)fUnknown).Predicate;
                if (pEffect != Utilities.TRUE_PREDICATE)
                {
                    lEffects.Add(pEffect);
                    AddReasoningAction(lAssigned, lEffects, dActions);
                }
                return;
            }
            CompoundFormula cfUnknown = (CompoundFormula)fUnknown;
            if (cfUnknown.Operator == "and")
            {
                bool bAllKnown = true;
                foreach (Formula f in cfUnknown.Operands)
                    if (f is CompoundFormula)
                        bAllKnown = false;
                if (bAllKnown)
                {
                    AddReasoningAction(lAssigned, lUnassigned, dActions);
                    return;
                }
            }
            Formula fReduced = null;
            foreach (Predicate p in lUnassigned)
            {
                HashSet<Predicate> lUnassignedReduced = new HashSet<Predicate>(lUnassigned);
                lUnassignedReduced.Remove(p);
                lAssigned.Add(p);
                fReduced = cfUnknown.Reduce(lAssigned);
                AddReasoningActions(fReduced, lUnassignedReduced, lAssigned, dActions);
                lAssigned.Remove(p);
                lAssigned.Add(p.Negate());
                fReduced = cfUnknown.Reduce(lAssigned);
                AddReasoningActions(fReduced, lUnassignedReduced, lAssigned, dActions);
                lAssigned.Remove(p.Negate());
            }
        }

        private bool IsRedundant(List<Predicate> lPreconditions, List<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            if (lPreconditions.Count == 0)
                return false;
            else
            {
                foreach (Predicate p in lPreconditions)
                {
                    List<Predicate> lReduced = new List<Predicate>();
                    foreach (Predicate pOther in lPreconditions)
                        if (p != pOther)
                            lReduced.Add(pOther);
                    if (dActions.ContainsKey(lReduced))
                    {
                        List<Predicate> lContainingActionEffects = dActions[lReduced];
                        foreach (Predicate pEffect in lEffects)
                            if (!lContainingActionEffects.Contains(pEffect))
                                return false;
                        return true;
                    }
                    if (IsRedundant(lReduced, lEffects, dActions))
                        return true;
                }
                return false;
            }
        }
        private Dictionary<List<Predicate>, List<Predicate>> FilterRedundancies(Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            Dictionary<List<Predicate>, List<Predicate>> dFiltered = new Dictionary<List<Predicate>, List<Predicate>>();
            foreach (KeyValuePair<List<Predicate>, List<Predicate>> p in dActions)
            {
                if (!IsRedundant(p.Key, p.Value, dActions))
                    dFiltered[p.Key] = p.Value;
            }
            return dFiltered;
        }

        private int WriteReasoningActions(StreamWriter sw, CompoundFormula cfHidden, int cActions, bool bRequireP)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cfHidden.GetAllPredicates(lPredicates);
            Dictionary<HashSet<Predicate>, HashSet<Predicate>> dActions = new Dictionary<HashSet<Predicate>, HashSet<Predicate>>();
            if (cfHidden.IsSimpleFormula())
            {
                SimpleAddReasoningActions(cfHidden, lPredicates, dActions, bRequireP);
            }
            else
            {
                throw new NotImplementedException();
            }
            foreach (KeyValuePair<HashSet<Predicate>, HashSet<Predicate>> pair in dActions)
            {

                HashSet<Predicate> lRemoveNotK = new HashSet<Predicate>(pair.Value);
                WriteResoningAction(sw, pair.Key, lRemoveNotK, cActions);
                cActions++;
            }
            return cActions;
        }

        private int WriteReasoningAxioms(StreamWriter sw, CompoundFormula cfHidden, int cActions)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cfHidden.GetAllPredicates(lPredicates);
            Dictionary<HashSet<Predicate>, HashSet<Predicate>> dActions = new Dictionary<HashSet<Predicate>, HashSet<Predicate>>();
            if (cfHidden.IsSimpleFormula())
            {
                SimpleAddReasoningActions(cfHidden, lPredicates, dActions, false);
            }
            else
            {
                throw new NotImplementedException();
            }
            foreach (KeyValuePair<HashSet<Predicate>, HashSet<Predicate>> p in dActions)
            {
                if (p.Value.Count == 1)
                {
                    throw new NotImplementedException();
                    //KnowPredicate kp = (KnowPredicate)p.Value.First();
                    //GroundedPredicate pOrg = (GroundedPredicate)kp.Knowledge;
                    //GroundedPredicate gpNotK = new GroundedPredicate(pOrg);
                    //gpNotK.Name = "NotK" + gpNotK.Name;
                    //p.Key.Add(gpNotK);
                }
                WriteResoningAxiom(sw, p.Key, p.Value, cActions);
                cActions++;
            }
            return cActions;
        }


        private void SimpleAddReasoningActions(CompoundFormula cf, HashSet<Predicate> lPredicates, Dictionary<HashSet<Predicate>, HashSet<Predicate>> dActions, bool bRequireP)
        {
            HashSet<Predicate> lPreconditions = null;
            HashSet<Predicate> lEffects = null;
            if (cf.Operator == "oneof")
            {
                foreach (Predicate p in lPredicates)
                {
                    //Kp and p -> K everything else is false
                    lPreconditions = new HashSet<Predicate>();
                    lPreconditions.Add(Predicate.GenerateKnowPredicate(p));
                    if (bRequireP)
                        lPreconditions.Add(p);

                    lEffects = new HashSet<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                    {
                        if (pOther != p)
                        {
                            if (bRequireP)
                                lPreconditions.Add(pOther.Negate());
                            lEffects.Add(Predicate.GenerateKnowPredicate(pOther.Negate()));
                        }
                    }
                    dActions[lPreconditions] = lEffects;

                    //K everything but p is false -> Kp
                    lPreconditions = new HashSet<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                    {
                        if (pOther != p)
                        {
                            if (bRequireP)
                                lPreconditions.Add(pOther.Negate());
                            lPreconditions.Add(Predicate.GenerateKnowPredicate(pOther.Negate()));
                        }
                    }
                    lEffects = new HashSet<Predicate>();
                    lEffects.Add(Predicate.GenerateKnowPredicate(p));
                    if (bRequireP)
                        lPreconditions.Add(p);

                    if (!lEffects.IsSubsetOf(lPreconditions))
                        dActions[lPreconditions] = lEffects;
                }
            }
            else if (cf.Operator == "or")
            {
                foreach (Predicate p in lPredicates)
                {
                    //K everything but p and everything is false -> Kp
                    lPreconditions = new HashSet<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                    {
                        if (pOther != p)
                        {
                            if (bRequireP)
                                lPreconditions.Add(pOther.Negate());
                            lPreconditions.Add(Predicate.GenerateKnowPredicate(pOther.Negate()));
                        }
                    }
                    lEffects = new HashSet<Predicate>();
                    lEffects.Add(Predicate.GenerateKnowPredicate(p));
                    if (bRequireP)
                        lPreconditions.Add(p);

                    if (!lEffects.IsSubsetOf(lPreconditions))
                        dActions[lPreconditions] = lEffects;
                }
            }
            else if (cf.Operator == "and")
            {
                throw new NotImplementedException("I don't think we can get here");
            }
        }

        private int WriteReasoningActionsII(StreamWriter sw, CompoundFormula cfHidden, int cStart)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cfHidden.GetAllPredicates(lPredicates);
            int cCurrent = cStart;
            foreach (GroundedPredicate pEffect in lPredicates)
            {
                sw.WriteLine("(:action R" + cCurrent);
                sw.Write(":precondition (and");
                foreach (GroundedPredicate pPrecondition in lPredicates)
                {
                    if (pPrecondition != pEffect)
                    {
                        sw.Write(" (K" + pPrecondition.Name);
                        foreach (Constant c in pPrecondition.Constants)
                            sw.Write(" " + c.Name);
                        sw.Write(")");
                    }
                }
                sw.WriteLine(")");
                sw.Write(":effect (K" + pEffect.Name);
                foreach (Constant c in pEffect.Constants)
                    sw.Write(" " + c.Name);
                sw.WriteLine(")");
                sw.WriteLine(")");
                cCurrent++;
            }
            return cCurrent;
        }

        public State WriteKReplannerProblem(string sFileName, BeliefState bsInitial)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (problem " + Name + ")");
            sw.WriteLine("(:domain " + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";
            foreach (GroundedPredicate gp in m_lKnown)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }


            //write invariants
            foreach (CompoundFormula cf in m_lHidden)
            {
                sw.WriteLine("\t" + cf.ToInvariant());
            }

            sw.WriteLine(")");

            //write hidden state
            sw.WriteLine("(:hidden");
            State s = bsInitial.ChooseState(false);
            foreach (GroundedPredicate gp in s.Predicates)
            {
                if (!m_lKnown.Contains(gp))
                {
                    sP = "";
                    if (gp.Negation)
                        sP = "(not ";
                    sP += "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    if (gp.Negation)
                        sP += ")";
                    sw.WriteLine("\t" + sP + ")");
                }
            }
            sw.WriteLine(")");

            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Close();
            return s;
        }

        public void AddMetric(string sMetricStatement)
        {
            MetricStatement = sMetricStatement;
        }

        private string GenerateKnowGivenLine(GroundedPredicate gp, string sTag, bool bKnowWhether)
        {
            if (gp.Name.ToLower() == "adj")
                Console.Write("*");

            string sKP = "";
            if (bKnowWhether)
                sKP = "(KWGiven" + gp.Name;
            else
            {
                if (Options.Translation == Options.Translations.SDR)
                    sKP = "(KGiven" + gp.Name;
                else
                    sKP = "(Given" + gp.Name;

            }
            foreach (Constant c in gp.Constants)
            {
                sKP += " " + c.Name;
            }

            sKP += " " + sTag;

            if (Options.Translation == Options.Translations.SDR)
            {
                if (gp.Negation)
                    sKP += " " + Utilities.FALSE_VALUE;
                else
                    sKP += " " + Utilities.TRUE_VALUE;
            }

            return sKP + ")";
        }

        private GroundedPredicate GenerateKnowGiven(GroundedPredicate gp, string sTag, bool bKnowWhether)
        {
            GroundedPredicate gpK = new GroundedPredicate("?");
            string sKP = "";
            if (bKnowWhether)
                gpK.Name = "KWGiven" + gp.Name;
            else
            {
                if (Options.Translation == Options.Translations.SDR)
                    gpK.Name = "KGiven" + gp.Name;
                else
                    gpK.Name = "Given" + gp.Name;

            }
            foreach (Constant c in gp.Constants)
            {
                gpK.AddConstant(c);
            }

            gpK.AddConstant(sTag, Utilities.TAG_PARAMETER);

            if (Options.Translation == Options.Translations.SDR)
            {
                if (gp.Negation)
                    gpK.AddConstant( Utilities.FALSE_VALUE, Utilities.VALUE_PARAMETER);
                else
                    gpK.AddConstant(Utilities.TRUE_VALUE, Utilities.VALUE_PARAMETER);
            }

            return gpK;
        }
        public MemoryStream WriteKnowledgeProblem(HashSet<Predicate> lObserved, HashSet<Predicate> lHidden, int cMinMishaps, int cMishaps)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine(";;" + Options.Translation);
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "", sP = "";

            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice")
                    continue;
                if (Domain.AlwaysKnown(gp))
                    sw.WriteLine(gp);
                if (!Domain.AlwaysKnown(gp))
                {
                    Predicate kp = Predicate.GenerateKnowPredicate(gp);
                    sw.WriteLine(kp);
                }

            }
            foreach (GroundedPredicate gp in lHidden)
            {
                //GroundedPredicate kp = new GroundedPredicate(gp);
                //kp.Name = "NotK" + kp.Name;
                //sw.WriteLine(kp);
            }

            if (cMinMishaps > cMishaps)
            {
                sw.WriteLine("(MishapCount m" + cMishaps + ")");
            }

            sw.WriteLine(")");

            ISet<Predicate> lGoalPredicates = Goal.GetAllPredicates();


            CompoundFormula cfGoal = new CompoundFormula("and");
            foreach (Predicate p in lGoalPredicates)
            {
                if (Domain.AlwaysKnown(p))
                    cfGoal.AddOperand(p);
                else
                    cfGoal.AddOperand(Predicate.GenerateKnowPredicate(p));
            }

            CompoundFormula cfAnd = new CompoundFormula(cfGoal);
            if (cMinMishaps > cMishaps && Options.Translation != Options.Translations.Conformant)
            {
                GroundedPredicate gp = new GroundedPredicate("MishapCount");
                gp.AddConstant(new Constant("mishaps", "m" + cMinMishaps));
                cfAnd.AddOperand(gp);
            }

            sw.WriteLine("(:goal " + cfAnd.Simplify() + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Flush();


            return msProblem;
        }


        public MemoryStream WriteKnowledgeProblem(HashSet<Predicate> lObserved, HashSet<Predicate> lAllValues)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine(";;" + Options.Translation);
            sw.WriteLine("(:init"); //ff doesn't like the and (and");


            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice")
                    continue;
                sw.WriteLine(gp);
                if (!Domain.AlwaysKnown(gp))
                {
                    Predicate kp = Predicate.GenerateKnowPredicate(gp);
                    sw.WriteLine(kp);
                }

            }
            HashSet<Predicate> lHidden = new HashSet<Predicate>(lAllValues.Except(lObserved));



            foreach (GroundedPredicate gp in lHidden)
            {
                sw.WriteLine(gp);
            }



            sw.WriteLine(")");

            ISet<Predicate> lGoalPredicates = Goal.GetAllPredicates();


            CompoundFormula cfGoal = new CompoundFormula("and");
            foreach (Predicate p in lGoalPredicates)
            {
                if (Domain.AlwaysKnown(p))
                    cfGoal.AddOperand(p);
                else
                    cfGoal.AddOperand(Predicate.GenerateKnowPredicate(p));
            }

            CompoundFormula cfAnd = new CompoundFormula(cfGoal);

            sw.WriteLine("(:goal " + cfAnd.Simplify() + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Flush();


            return msProblem;
        }


        public MemoryStream WriteTaggedProblem(Dictionary<string, ISet<Predicate>> dTags, CompoundFormula cfGoal, ISet<Predicate> lObserved,
                                        ISet<Predicate> lTrueState, Dictionary<string, double> dFunctionValues, Options.DeadendStrategies dsStrategy)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "", sP = "";
            if (Options.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            if (Options.SplitConditionalEffects)
                sw.WriteLine("(NotInAction)\n");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice")
                    continue;
                sKP = "(K" + gp.Name;
                sP = "(" + gp.Name;
                foreach (Constant c in gp.Constants)
                {
                    sKP += " " + c.Name;
                    sP += " " + c.Name;
                }
                if (gp.Negation)
                    sKP += " " + Utilities.FALSE_VALUE;
                else
                    sKP += " " + Utilities.TRUE_VALUE;
                if (!Domain.AlwaysKnown(gp))
                    sw.WriteLine(sKP + ")");
                if (!gp.Negation)
                    sw.WriteLine(sP + ")");
            }
            foreach (GroundedPredicate gp in lTrueState)
            {
                if (gp.Name == "Choice")
                    continue;
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine(sP + ")");
                }
            }
            foreach (KeyValuePair<string, ISet<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Name == "Choice")
                        continue;
                    sKP = GenerateKnowGivenLine(gp, p.Key, false);
                    sw.WriteLine(sKP);
                }

                if (Options.AddAllKnownToGiven)
                {
                    foreach (GroundedPredicate gp in lObserved)
                    {
                        if (gp.Name == "Choice")
                            continue;
                        if (!Domain.AlwaysKnown(gp))
                        {
                            sKP = GenerateKnowGivenLine(gp, p.Key, false);
                            sw.WriteLine(sKP);
                        }
                    }
                }

            }


            sw.WriteLine(")");

            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            cfGoal.GetAllPredicates(lGoalPredicates);

            foreach (Predicate p in lGoalPredicates)
            {
                if (!Domain.AlwaysKnown(p))
                    cfGoal.AddOperand(Predicate.GenerateKnowPredicate(p));
            }


            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Flush();


            return msProblem;
        }



        public Problem CreateTaggedProblem(Domain dTagged, Dictionary<string, ISet<Predicate>> dTags, ISet<Predicate> lObserved,
                                        ISet<Predicate> lTrueState, Dictionary<string, double> dFunctionValues, Options.DeadendStrategies dsStrategy,
                                        bool bPreconditionFailure)
        {
            Problem problem = new Problem("K" + Name, dTagged);

            if (Options.TIME_STEPS > 0)
            {
                GroundedPredicate gpTime = new GroundedPredicate("time0");
                problem.AddKnown(gpTime);
            }


            if (Options.SplitConditionalEffects)
                throw new NotImplementedException();

            if(dFunctionValues != null && dFunctionValues.Count > 0)
                throw new NotImplementedException();

            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice" || gp.Name.ToLower().Contains(Utilities.OPTION_PREDICATE))
                    continue;
                GroundedPredicate gpK = new GroundedPredicate("K" + gp.Name);
                if (gp.Negation)
                    gpK.Name = "KN" + gp.Name;
                
                foreach (Constant c in gp.Constants)
                {
                    gpK.AddConstant(c);
                }
                

                if (!Domain.AlwaysKnown(gp))
                    problem.AddKnown(gpK);
                if (!gp.Negation)
                    problem.AddKnown(gp);
            }
            foreach (GroundedPredicate gp in lTrueState)
            {
                if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                    continue;
                problem.AddKnown(gp);
            }
            foreach (KeyValuePair<string, ISet<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                        continue;
                    GroundedPredicate gpK = GenerateKnowGiven(gp, p.Key, false);
                    problem.AddKnown(gpK);
                }

                if (Options.AddAllKnownToGiven)
                {
                    foreach (GroundedPredicate gp in lObserved)
                    {
                        if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                            continue;
                        if (!Domain.AlwaysKnown(gp))
                        {
                            GroundedPredicate gpK = GenerateKnowGiven(gp, p.Key, false);
                            problem.AddKnown(gpK);
                        }
                    }
                }

            }


            

            CompoundFormula cfTrueGoal = new CompoundFormula("and");
            CompoundFormula cfIdentificationGoal = new CompoundFormula("and");

            for (int i = 1; i < dTags.Keys.Count; i++)
            {
                Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, dTags.Keys.ElementAt(i)));
                cfIdentificationGoal.AddOperand(pKNotT);
            }

            cfTrueGoal.AddOperand(Goal);
            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            cfTrueGoal.GetAllPredicates(lGoalPredicates);

            foreach (Predicate p in lGoalPredicates)
            {
                if (!Domain.AlwaysKnown(p))
                    cfTrueGoal.AddOperand(Predicate.GenerateKnowPredicate(p));
            }

            CompoundFormula cfGoal = null;
            if (dsStrategy == Options.DeadendStrategies.Active)
            {
                cfGoal = cfIdentificationGoal;
            }
            if (dsStrategy == Options.DeadendStrategies.Lazy)
            {
                cfGoal = cfTrueGoal;
            }
            if (dsStrategy == Options.DeadendStrategies.Both)
            {
                cfGoal = new CompoundFormula("or");
                cfGoal.AddOperand(cfTrueGoal);
                cfGoal.AddOperand(cfIdentificationGoal);
            }

            if (bPreconditionFailure && dTags.Keys.Count > 1)
            {
                cfGoal = cfIdentificationGoal;
                //cfGoal.AddOperand(cfIdentificationGoal);
            }

            if (cfGoal.Operands.Count == 0)
                Console.Write("*");

            problem.Goal = cfGoal;

            if (MetricStatement != null)
            {
                throw new NotImplementedException();
            }
            


            return problem;
        }


        public MemoryStream WriteTaggedProblem(Dictionary<string, List<Predicate>> dTags, ISet<Predicate> lObserved,
                                        List<Predicate> lTrueState, Dictionary<string, double> dFunctionValues, Options.DeadendStrategies dsStrategy)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");


            string sKP = "", sP = "";
            if (Options.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            if (Options.SplitConditionalEffects)
                sw.WriteLine("(NotInAction)\n");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice" || gp.Name.ToLower().Contains(Utilities.OPTION_PREDICATE))
                    continue;
                if (gp.Negation)
                    sKP = "(KN" + gp.Name;
                else
                    sKP = "(K" + gp.Name;
                sP = "(" + gp.Name;
                foreach (Constant c in gp.Constants)
                {
                    sKP += " " + c.Name;
                    sP += " " + c.Name;
                }
                /*
                if (gp.Negation)
                    sKP += " " + Utilities.FALSE_VALUE;
                else
                    sKP += " " + Utilities.TRUE_VALUE;
                    */
                if (!Domain.AlwaysKnown(gp))
                    sw.WriteLine(sKP + ")");
                if (!gp.Negation)
                    sw.WriteLine(sP + ")");
            }
            foreach (GroundedPredicate gp in lTrueState)
            {
                if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                    continue;
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine(sP + ")");
                }
            }
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                        continue;
                    sKP = GenerateKnowGivenLine(gp, p.Key, false);
                    sw.WriteLine(sKP);
                }

                if (Options.AddAllKnownToGiven)
                {
                    foreach (GroundedPredicate gp in lObserved)
                    {
                        if (gp.Name == "Choice" || gp.Name.ToLower().Contains("_" + Utilities.OPTION_PREDICATE))
                            continue;
                        if (!Domain.AlwaysKnown(gp))
                        {
                            sKP = GenerateKnowGivenLine(gp, p.Key, false);
                            sw.WriteLine(sKP);
                        }
                    }
                }

            }


            sw.WriteLine(")");

            CompoundFormula cfTrueGoal = new CompoundFormula("and");
            CompoundFormula cfIdentificationGoal = new CompoundFormula("and");

            for (int i = 1; i < dTags.Keys.Count; i++)
            {
                Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, dTags.Keys.ElementAt(i)));
                cfIdentificationGoal.AddOperand(pKNotT);
            }

            cfTrueGoal.AddOperand(Goal);
            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            cfTrueGoal.GetAllPredicates(lGoalPredicates);

            foreach (Predicate p in lGoalPredicates)
            {
                if (!Domain.AlwaysKnown(p))
                    cfTrueGoal.AddOperand(Predicate.GenerateKnowPredicate(p));
            }

            CompoundFormula cfGoal = null;
            if (dsStrategy == Options.DeadendStrategies.Active)
            {
                cfGoal = cfIdentificationGoal;
            }
            if (dsStrategy == Options.DeadendStrategies.Lazy)
            {
                cfGoal = cfTrueGoal;
            }
            if (dsStrategy == Options.DeadendStrategies.Both)
            {
                cfGoal = new CompoundFormula("or");
                cfGoal.AddOperand(cfTrueGoal);
                cfGoal.AddOperand(cfIdentificationGoal);
            }
            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Flush();


            return msProblem;
        }



        public MemoryStream WriteTaggedProblemNoState(Dictionary<string, ISet<Predicate>> dTags, ISet<Predicate> lObserved,
                                                 Dictionary<string, double> dFunctionValues)
        {
            MemoryStream ms = new MemoryStream(1000);
            StreamWriter sw = new StreamWriter(ms);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "";
            if (Options.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                //if (gp.Negation)
                //    continue;
                if (gp.Name == "Choice" || gp.Name == Utilities.OPTION_PREDICATE)
                    continue;
                if (Domain.AlwaysKnown(gp) && Domain.AlwaysConstant(gp))
                {
                    sKP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sKP += " " + c.Name;
                    }
                    sw.WriteLine(sKP + ")");
                }
                else
                {
                    foreach (string sTag in dTags.Keys)
                    {
                        if (!gp.Negation)
                        {
                            Predicate pGiven = gp.GenerateGiven(sTag);
                            sw.WriteLine(pGiven);
                        }
                    }
                }
            }
            foreach (KeyValuePair<string, ISet<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Negation)
                        continue;
                    if (gp.Name == "Choice")
                        continue;
                    if (!gp.Negation)
                    {
                        sw.WriteLine(gp.GenerateGiven(p.Key));
                    }
                    //sKP = GenerateKnowGivenLine(gp, p.Key, true);
                    //sw.WriteLine(sKP);
                }

            }

            //if (Problem.Domain.HasNonDeterministicActions())
            //    sw.WriteLine("(option opt0)");

            //if (Options.SplitConditionalEffects)
            sw.WriteLine("(NotInAction)");

            sw.WriteLine(")");

            CompoundFormula cfGoal = new CompoundFormula("and");

            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            Goal.GetAllPredicates(lGoalPredicates);


            for (int iTag = 0; iTag < dTags.Count; iTag++)
            {
                if (Options.ConsiderStateNegations && iTag == dTags.Count - 1)
                    break;//What is that?
                string sTag = dTags.Keys.ElementAt(iTag);
                foreach (Predicate p in lGoalPredicates)
                {
                    if (!Domain.AlwaysKnown(p) || !Domain.AlwaysConstant(p))
                    {
                        cfGoal.AddOperand(p.GenerateGiven(sTag));
                    }
                }
            }

            if (Options.ForceTagObservations)
            {
                foreach (string sTag1 in dTags.Keys)
                    foreach (string sTag2 in dTags.Keys)
                        if (sTag1 != sTag2)
                        {
                            Predicate gpNot = Predicate.GenerateKNot(new Constant(Utilities.TAG, sTag1), new Constant(Utilities.TAG, sTag2));
                            cfGoal.AddOperand(gpNot);
                        }
            }

            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Flush();

            return ms;
        }


        public void WriteProblem(string sProblemFile)
        {
            StreamWriter sw = new StreamWriter(sProblemFile);
            sw.WriteLine("(define (problem " + Name + ")");
            sw.WriteLine("(:domain " + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";
            foreach (GroundedPredicate gp in Known)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }

            sw.WriteLine();

            foreach (CompoundFormula cf in Hidden)
                sw.WriteLine("\t" + cf);


            sw.WriteLine(")");



            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Close();
        }



        public MemoryStream WriteSimpleProblem(State sCurrent)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem " + Name + ")");
            sw.WriteLine("(:domain " + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";

            List<Predicate> lPredicates = null;
            if (sCurrent == null)
                lPredicates = new List<Predicate>(Known);
            else
                lPredicates = new List<Predicate>(sCurrent.Predicates);

            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }



            sw.WriteLine(")");



            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Flush();

            

            return msProblem;
        }


        public MemoryStream WriteDeadendDetectionProblem()
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem DED" + Name + ")");
            sw.WriteLine("(:domain DED" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";
            foreach (GroundedPredicate gp in Known)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }
            sw.WriteLine("(init)");
            sw.WriteLine("(init0)");



            sw.WriteLine(")");



            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Flush();

            bool bDone = false;
            while (!bDone)
            {
                try
                {
                    msProblem.Position = 0;
                    StreamReader sr = new StreamReader(msProblem);
                    
                    bDone = true;
                }
                catch (Exception e)
                { }
            }



            return msProblem;
        }

        public void RemoveUniversalQuantifiers()
        {
            Goal = Goal.RemoveUniversalQuantifiers(Domain.Constants, null, null);
        }

        public HashSet<GroundedPredicate> GetRelevantPredicates(GroundedPredicate gp)
        {
            if (gp.Negation)
                gp = (GroundedPredicate)gp.Negate();
            if (m_dRelevantPredicates.ContainsKey(gp))
                return m_dRelevantPredicates[gp];
            return new HashSet<GroundedPredicate>();
        }

        public bool IsRelevantFor(GroundedPredicate gp, GroundedPredicate gpRelevant)
        {
            if (!m_dRelevantPredicates.ContainsKey((GroundedPredicate)gp.Canonical()))
                return false;
            return m_dRelevantPredicates[(GroundedPredicate)gp.Canonical()].Contains((GroundedPredicate)gpRelevant.Canonical());
        }


        public void ComputeRelevanceClosure()
        {
            bool bDone = false;
            while (!bDone)
            {
                bDone = true;
                foreach (GroundedPredicate gp in m_dRelevantPredicates.Keys)
                {
                    HashSet<Predicate> hsCurrentRelevant = new HashSet<Predicate>(m_dRelevantPredicates[gp]);
                    foreach (GroundedPredicate gpRelevant in hsCurrentRelevant)
                    {
                        foreach (GroundedPredicate gpOther in m_dRelevantPredicates[gpRelevant])
                        {
                            if (!gpOther.Equals(gp))
                                if (m_dRelevantPredicates[gp].Add(gpOther))
                                    bDone = false;
                        }
                    }

                }
            }
        }

        private List<Predicate> m_lSATVariables = new List<Predicate>();
        private Dictionary<Predicate, int> m_dSATVariables = new Dictionary<Predicate, int>();
        public int GetPredicateIndex(Predicate p)
        {
            bool bNegate = p.Negation;
            if (bNegate)
                p = p.Negate();
            if (!m_dSATVariables.ContainsKey(p))
            {
                m_dSATVariables[p] = m_dSATVariables.Count + 1;
                m_lSATVariables.Add(p);
            }
            int idx = m_dSATVariables[p];
            return idx;
        }

        public Predicate GetPredicateByIndex(int idx)
        {
            if (idx >= 0 && idx < m_lSATVariables.Count)
                return m_lSATVariables[idx];
            return null;
        }

        public string GetPredicateString(Predicate p)
        {
            int idx = GetPredicateIndex(p);
            if (p.Negation)
                return "-" + idx;
            return "" + idx;
        }

        public int GetSATVariablesCount()
        {
            return m_dSATVariables.Count;
        }

        public bool Ready { get; set; }

        public void PrepareForPlanning()
        {
            if (!Ready)
            {
                Domain.ComputeAlwaysKnown();
                CompleteKnownState();


                List<Predicate> lConstantPredicates = new List<Predicate>();
                foreach (Predicate pKnown in Known)
                {
                    if (Domain.AlwaysConstant(pKnown))
                        lConstantPredicates.Add(pKnown);
                }
                Domain.RemoveUniversalQuantifiers(lConstantPredicates);
                RemoveUniversalQuantifiers();

                Ready = true;
            }
        }
    }
}
