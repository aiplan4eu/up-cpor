using System;

using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using CPORLib.Algorithms;
using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.Tools;

namespace CPORLib.PlanningModel
{
    public class Domain
    {
        public string Name { get; protected set; }
        public List<string> Types { get; private set; }

        public Dictionary<string, string> TypeHierarchy { get; private set; }
        public List<PlanningAction> Actions { get; set; }
        public List<Constant> Constants { get; protected set; }
        public List<Predicate> Predicates { get; protected set; }
        public List<string> Functions { get; protected set; }
        public List<string> m_lAlwaysKnown { get; protected set; }
        private List<string> m_lAlwaysConstant;
        private List<string> m_lObservable;

        public bool IsSimple { get; private set; }


        public bool UseCosts { get; private set; }


        private Dictionary<Predicate, Predicate> m_dAuxilaryPredicates;

        public bool ContainsNonDeterministicActions { get; private set; }

        public Domain(string sName)
        {
            UseCosts = true;
            Name = sName;
            Actions = new List<PlanningAction>();
            Constants = new List<Constant>();
            Predicates = new List<Predicate>();
            Types = new List<string>();
            m_lAlwaysKnown = new List<string>();
            m_lAlwaysKnown.Add("increase");
            m_lAlwaysKnown.Add("decrease");
            m_lAlwaysKnown.Add("=");
            m_lAlwaysConstant = new List<string>();
            m_lObservable = new List<string>();
            m_dAuxilaryPredicates = new Dictionary<Predicate, Predicate>();
            Functions = new List<string>();
            IsSimple = true;
            ContainsNonDeterministicActions = false;
            TypeHierarchy = new Dictionary<string, string>();
        }


        #region accessors for unified_planning 

        public void AddType(string sType)
        {
            if(!Types.Contains(sType))
                Types.Add(sType);
        }
        public void AddType(string sType, string sParentType)
        {
            if (!Types.Contains(sType))
            {
                Types.Add(sType);
            }
            if (!Types.Contains(sParentType))
                Types.Add(sParentType);
            TypeHierarchy[sType] = sParentType;
        }



        #endregion


        public void AddAction(PlanningAction a)
        {
            if(a is ParametrizedAction pa)
                pa.FixParametersNames();
            Actions.Add(a);
            if (a.Effects != null)
            {
                HashSet<Predicate> lConditionalEffects = new HashSet<Predicate>();
                HashSet<Predicate> lNonConditionalEffects = new HashSet<Predicate>();

                a.Effects.GetAllEffectPredicates(lConditionalEffects, lNonConditionalEffects);

                if (lConditionalEffects.Count > 0)
                    IsSimple = false;

                foreach (Predicate p in lConditionalEffects)
                {
                    //m_lAlwaysKnown.Remove(p.Name);
                    m_lAlwaysConstant.Remove(p.Name);
                }
                foreach (Predicate p in lNonConditionalEffects)
                {
                    m_lAlwaysConstant.Remove(p.Name);
                }
                List<Predicate> lNonDetEffects = a.GetNonDeterministicEffects();
                if (lNonDetEffects != null)
                {
                    foreach (Predicate p in lNonDetEffects)
                    {
                        m_lAlwaysKnown.Remove(p.Name);
                    }
                }

            }
            else if (a.Effects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)a.Effects).Predicate;
                m_lAlwaysConstant.Remove(p.Name);
            }
            if (a.Observe != null)
            {
                foreach (Predicate p in a.Observe.GetAllPredicates())
                    m_lObservable.Add(p.Name);
            }
            if (a.ContainsNonDeterministicEffect)
                ContainsNonDeterministicActions = true;
        }
        public void AddConstant(Constant c)
        {
            Constants.Add(c);
        }
        public void AddConstant(string sName, string sType)
        {
            Constant c = new Constant(sType, sName);
            AddConstant(c);
        }
        public void AddPredicate(Predicate p)
        {
            if(p is ParametrizedPredicate pp)
            {
                ParametrizedPredicate ppNew = new ParametrizedPredicate(pp.Name);
                foreach(Parameter param in pp.Parameters)
                {
                    string sName = param.Name;
                    if (!sName.StartsWith("?"))
                        sName = "?" + sName;
                    Parameter paramNew = new Parameter(param.Type, sName);
                    ppNew.AddParameter(paramNew);
                }
                p = ppNew; 
            }
            Predicates.Add(p);
            m_lAlwaysKnown.Add(p.Name);
            m_lAlwaysConstant.Add(p.Name);
        }
        public override string ToString()
        {
            string s = "(domain " + Name + "\n";
            s += "(constants " + Utilities.ListToString(Constants) + ")\n";
            s += "(predicates " + Utilities.ListToString(Predicates) + ")\n";
            s += "(actions " + Utilities.ListToString(Actions) + ")\n";
            s += ")";
            return s;
        }

        //not really checking everything - need to check compatible parameters, constants and so forth
        public bool ContainsPredicate(string sName)
        {
            foreach (Predicate p in Predicates)
                if (p.Name == sName)
                    return true;
            return false;
        }

        public Constant GetConstant(string sName)
        {
            foreach (Constant c in Constants)
                if (c.Name == sName)
                    return c;
            return null;
        }


        MemoryStream m_sCachedDomain = null;

        public MemoryStream WriteKnowledgeDomain(Problem p, int ciMishapCount, int cMinMishapCount, bool bMishapType, bool bRequireP)
        {
            if (m_sCachedDomain == null)
            {
                StreamWriter sw = null;
                MemoryStream ms = new MemoryStream(1000);
                sw = new StreamWriter(ms);

                sw.WriteLine("(define (domain K" + Name + ")");
                sw.WriteLine("(:requirements :strips :typing)");
                sw.WriteLine(";;" + Options.Translation);
                WriteTypes(sw, false);
                WriteConstants(sw, cMinMishapCount, ciMishapCount);
                sw.WriteLine();
                WriteKnowledgePredicates(sw, cMinMishapCount, ciMishapCount, bRequireP);
                sw.WriteLine();
                WriteKnowledgeActions(sw, cMinMishapCount, ciMishapCount, bMishapType, bRequireP);
                p.WriteReasoningActions(sw, bRequireP);
                //p.WriteReasoningAxioms(sw);
                sw.WriteLine(")");

                sw.Flush();
                m_sCachedDomain = ms;
            }
            return m_sCachedDomain;
        }


        //know whether - no s_0
        public MemoryStream WriteTaggedDomainNoState(Dictionary<string, List<Predicate>> dTags, Problem pCurrent)
        {
            if (HasNonDeterministicActions() && Options.UseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();
                return dDeterministic.WriteTaggedDomainNoState(dTags, pCurrent);
            }


            StreamWriter sw = null;
            MemoryStream sm = new MemoryStream(1000);
            sw = new StreamWriter(sm);

            sw.WriteLine("(define (domain K" + Name + ")");



            sw.WriteLine("(:requirements :strips :typing)");

            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();
            if (Options.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<PlanningAction> lAllActions = GetKnowledgeActionsNoState(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicatesNoState(sw, lAdditionalPredicates);
                foreach (PlanningAction aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether, null);
                sw.WriteLine();

                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }
            else
            {
                WriteTaggedPredicatesNoState(sw, null);
                sw.WriteLine();
                WriteKnowledgeActionsNoState(sw, dTags);
                //WriteReasoningActionsNoState(sw, dTags, pCurrent);
            }


            sw.WriteLine(")");
            sw.Flush();



            return sm;
        }


        public MemoryStream WriteTaggedDomain(Dictionary<string, List<Predicate>> dTags, Problem pCurrent, List<Formula> lDeadends)
        {
            if (HasNonDeterministicActions() && Options.UseOptions)
            {
                Domain dDeterministic = RemoveNonDeterministicEffects();

                return dDeterministic.WriteTaggedDomain(dTags, pCurrent, lDeadends);
            }


            StreamWriter sw = null;
            MemoryStream strStream = new MemoryStream(1000);

            //sw = new StreamWriter(sFileName);
            sw = new StreamWriter(strStream);

            sw.WriteLine("(define (domain K" + Name + ")");


            sw.WriteLine("(:requirements :strips :typing)");

            WriteFunctions(sw);
            WriteTypes(sw, true);
            WriteConstants(sw, dTags);
            sw.WriteLine();


            if (Options.SplitConditionalEffects)
            {
                List<Predicate> lAdditionalPredicates = new List<Predicate>();
                List<PlanningAction> lAllActions = GetKnowledgeActions(sw, dTags, lAdditionalPredicates);
                WriteTaggedPredicates(sw, lAdditionalPredicates);
                foreach (PlanningAction aKnowWhether in lAllActions)
                    WriteConditionalAction(sw, aKnowWhether, lDeadends);
                sw.WriteLine();

                WriteReasoningActions(sw, dTags, pCurrent, lDeadends);
            }
            else
            {
                WriteTaggedPredicates(sw, null);
                sw.WriteLine();
                WriteKnowledgeActions(sw, dTags, lDeadends);
                WriteReasoningActions(sw, dTags, pCurrent, lDeadends);
            }




            if (Options.RemoveConflictingConditionalEffects)
                WriteAxiomsActions(sw, dTags);

            sw.WriteLine(")");
            sw.Flush();
            //sw.Close();//shouldn't close the mem stream

            return strStream;
        }

        private void WriteFunctions(StreamWriter sw)
        {
            if (Functions.Count > 0)
            {
                sw.Write("(:functions");
                foreach (string sFunction in Functions)
                    sw.Write(" " + sFunction);
                sw.WriteLine(")");

            }
        }

        private Domain RemoveNonDeterministicEffects()
        {
            Domain dDeterministic = new Domain(Name);
            dDeterministic.Predicates = new List<Predicate>(Predicates);
            dDeterministic.Constants = new List<Constant>(Constants);
            dDeterministic.Types = new List<string>(Types);
            dDeterministic.Actions = new List<PlanningAction>();
            dDeterministic.m_lAlwaysKnown = m_lAlwaysKnown;
            dDeterministic.m_lAlwaysConstant = m_lAlwaysConstant;
            dDeterministic.m_dConstantNameToType = m_dConstantNameToType;
            dDeterministic.Functions = Functions;

            dDeterministic.Types.Add(Utilities.OPTION);
            dDeterministic.m_lAlwaysConstant.Add(Utilities.OPTION_PREDICATE);
            //dDeterministic.m_lAlwaysKnown.Add(Utilities.OPTION_PREDICATE);

            ParametrizedPredicate ppOption = new ParametrizedPredicate(Utilities.OPTION_PREDICATE);
            ppOption.AddParameter(new Parameter(Utilities.OPTION, "?o"));
            dDeterministic.Predicates.Add(ppOption);

            int cOptions = Math.Max(MaxNonDeterministicEffects(), Options.MAX_OPTIONS);
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                dDeterministic.Constants.Add(new Constant(Utilities.OPTION, "opt" + iOption));
            }

            if (Options.AllowChoosingNonDeterministicOptions)
            {
                PlanningAction aChoose = new PlanningAction("AdvanceOptions");
                CompoundFormula cfEffects = new CompoundFormula("and");
                for (int iOption = 0; iOption < Options.MAX_OPTIONS; iOption++)
                {
                    GroundedPredicate gpCurrentOption = new GroundedPredicate(Utilities.OPTION_PREDICATE);
                    gpCurrentOption.AddConstant(new Constant(Utilities.OPTION, "opt" + iOption));
                    GroundedPredicate gpNextOption = new GroundedPredicate(Utilities.OPTION_PREDICATE);
                    gpNextOption.AddConstant(new Constant(Utilities.OPTION, "opt" + (iOption + 1) % Options.MAX_OPTIONS));
                    CompoundFormula cfWhen = new CompoundFormula("when");
                    cfWhen.AddOperand(gpCurrentOption);
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    cfAnd.AddOperand(gpCurrentOption.Negate());
                    cfAnd.AddOperand(gpNextOption);
                    cfWhen.AddOperand(cfAnd);
                    cfEffects.AddOperand(cfWhen);
                }

                aChoose.Effects = cfEffects;
                dDeterministic.AddAction(aChoose);
            }

            foreach (PlanningAction a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    PlanningAction aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown, Options.MAX_OPTIONS);
                    dDeterministic.Actions.Add(aDeterministic);
                }
                else
                {
                    dDeterministic.Actions.Add(a);
                }
            }

            return dDeterministic;
        }

        private string GeneratePredicateAxiom(GroundedPredicate gp, string sPrefix, string sAdditionalConstants)
        {
            string sGiven = "(Not-" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sGiven += " " + p.Name;
            sGiven += sAdditionalConstants;
            sGiven += ")";
            string sEffect = "(and (not " + sGiven + ")";
            sEffect += " (not ";
            sEffect += "(" + sPrefix + gp.Name;
            foreach (Constant p in gp.Constants)
                sEffect += " " + p.Name;
            sEffect += sAdditionalConstants;
            sEffect += ")))";
            string s = "(when " + sGiven + " " + sEffect + ")";
            return s;
        }

        private void WriteAxiomsAction(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (not (axioms-applied))\n");
            sw.WriteLine("\t:effect (and (axioms-applied)\n");

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate pp in lGrounded)
            {
                sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "", ""));

                if (!AlwaysKnown(pp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + Utilities.TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "K", " " + Utilities.FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + Utilities.TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(pp, "KGiven", " " + sTag + " " + Utilities.FALSE_VALUE));

                    }
                }
            }
            sw.WriteLine("))");
        }


        private void WriteAxiomsActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {

            HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.WriteLine("(:action apply-axioms-" + gp.Name);
                sw.WriteLine("\t:precondition (not (axioms-applied))");
                sw.WriteLine("\t:effect (and ");

                sw.Write("(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");


                sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "", ""));

                if (!AlwaysKnown(gp))
                {
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + Utilities.TRUE_VALUE));
                    sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "K", " " + Utilities.FALSE_VALUE));

                    foreach (string sTag in dTags.Keys)
                    {
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + Utilities.TRUE_VALUE));
                        sw.WriteLine("\t\t" + GeneratePredicateAxiom(gp, "KGiven", " " + sTag + " " + Utilities.FALSE_VALUE));

                    }
                }
                sw.WriteLine("))");
            }
            sw.WriteLine("(:action apply-axioms");
            sw.WriteLine("\t:precondition (and (not (axioms-applied))");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine(")");
            }
            sw.WriteLine(")");
            sw.WriteLine("\t:effect (and (axioms-applied)");
            foreach (GroundedPredicate gp in lGrounded)
            {
                sw.Write("\t\t(not (axioms-applied-" + gp.Name);
                foreach (Constant c in gp.Constants)
                    sw.Write("-" + c.Name);
                sw.WriteLine("))");
            }
            sw.WriteLine("))");

        }


        private void WriteKnowledgePreconditions(StreamWriter sw, PlanningAction pa)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            pa.Preconditions.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (Predicate p in lPredicates)
            {
                if (AlwaysKnown(p))
                {
                    cfAnd.AddOperand(p);
                }
                else
                {
                    cfAnd.AddOperand(new KnowPredicate(p));
                }
            }
            sw.WriteLine(":precondition " + cfAnd);

            /*
            sw.Write(":precondition (and");
            foreach (Formula f in cfAnd.Operands)
                sw.Write(" " + f.ToString());
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            
            sw.WriteLine(")");
             * */

        }

        public void WriteKnowledgePredicate(StreamWriter sw, Predicate p)
        {
            if (!AlwaysKnown(p))
                sw.Write(new KnowPredicate(p).ToString());
        }
        private void WriteKnowledgeEffects(StreamWriter sw, PlanningAction pa, List<Predicate> lKnow)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            if (pa.Effects != null)
                pa.Effects.GetAllPredicates(lPredicates);
            if (pa.Observe != null)
                pa.Observe.GetAllPredicates(lPredicates);
            CompoundFormula cfAnd = (CompoundFormula)pa.Effects;
            if (cfAnd != null && cfAnd.Operator != "and")
                throw new NotImplementedException();
            sw.Write(":effect (and");
            if (cfAnd != null)
            {
                foreach (Formula f in cfAnd.Operands)
                    sw.Write(" " + f.ToString());
            }
            foreach (Predicate p in lPredicates)
            {
                if (lKnow == null || lKnow.Contains(p))
                {
                    WriteKnowledgePredicate(sw, p);
                }
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgeAction(StreamWriter sw, PlanningAction a, int cMinMishaps, int cMishaps, bool bMishapType, bool bRequireP)
        {
            PlanningAction aK = a.Clone();

            if (a.Preconditions != null)
                aK.Preconditions = aK.Preconditions.GetKnowledgeFormula(m_lAlwaysKnown, false);

            if (a.Effects != null)
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(aK.Effects.GetKnowledgeFormula(m_lAlwaysKnown, false));
                //if (a.NonDeterministicEffects.Count > 0)
                //    throw new NotImplementedException();

                foreach (Predicate p in a.NonDeterministicEffects)
                {
                    Predicate pKnow = new KnowPredicate(p);
                    cfAnd.AddOperand(pKnow.Negate());
                }
                aK.Effects = cfAnd.Simplify();
            }

            if (a.Observe == null || Options.Translation == Options.Translations.Conformant)
            {
                if (a.Effects != null)
                {
                    a.Observe = null;
                    sw.WriteLine(aK);
                }
            }
            else
            {

                if (aK.Effects == null)
                    aK.Effects = new CompoundFormula("and");
                aK.Observe = null;
                Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                KnowPredicate kp = new KnowPredicate(pObserve);
                KnowPredicate knp = new KnowPredicate(pObserve.Negate());

                CompoundFormula cfPreconditions = new CompoundFormula("and");
                cfPreconditions.AddOperand(kp.Negate());
                cfPreconditions.AddOperand(knp.Negate());
                cfPreconditions.AddOperand(aK.Preconditions);
                aK.Preconditions = cfPreconditions.Simplify();

                //Predicate gpNotK = pObserve.Clone();
                //gpNotK.Name = "NotK" + gpNotK.Name;

                PlanningAction aKT = aK.Clone();
                aKT.Name += "T";
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(aKT.Preconditions);
                if (bRequireP)
                    cfAnd.AddOperand(pObserve);
                //cfAnd.AddOperand(gpNotK);
                //cfAnd.AddOperand(kp.Negate());
                //cfAnd.AddOperand(knp.Negate());
                aKT.Preconditions = cfAnd;
                ((CompoundFormula)aKT.Effects).AddOperand(kp);
                //((CompoundFormula)aKT.Effects).AddOperand(gpNotK.Negate());

                if (cMinMishaps > cMishaps && bMishapType)
                {
                    //AddMishapIncrease(aKT, cMinMishaps);
                    List<PlanningAction> lActions = AddMishapIncreaseNonConditional(aKT, cMinMishaps);
                    foreach (PlanningAction aMishap in lActions)
                        sw.WriteLine(aMishap);
                }
                else
                {
                    sw.WriteLine(aKT);
                }


                PlanningAction aKF = aK.Clone();
                aKF.Name += "F";
                cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(aKF.Preconditions);
                if (bRequireP)
                    cfAnd.AddOperand(pObserve.Negate());
                //cfAnd.AddOperand(kp.Negate());
                //cfAnd.AddOperand(knp.Negate());
                //cfAnd.AddOperand(gpNotK);

                aKF.Preconditions = cfAnd;
                ((CompoundFormula)aKF.Effects).AddOperand(knp);
                //((CompoundFormula)aKF.Effects).AddOperand(gpNotK.Negate());

                if (cMinMishaps > cMishaps && !bMishapType)
                {
                    //AddMishapIncrease(aKT, cMinMishaps);
                    List<PlanningAction> lActions = AddMishapIncreaseNonConditional(aKF, cMinMishaps);
                    foreach (PlanningAction aMishap in lActions)
                        sw.WriteLine(aMishap);
                }
                else
                {
                    sw.WriteLine(aKF);
                }


            }


        }

        private void AddMishapIncrease(PlanningAction a, int cMishaps)
        {
            CompoundFormula cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(a.Effects);
            for (int i = 0; i < cMishaps; i++)
            {
                CompoundFormula cfWhen = new CompoundFormula("when");
                GroundedPredicate gpBefore = new GroundedPredicate("MishapCount");
                gpBefore.AddConstant(new Constant("mishaps", "m" + i));
                GroundedPredicate gpAfter = new GroundedPredicate("MishapCount");
                gpAfter.AddConstant(new Constant("mishaps", "m" + (i + 1)));
                cfWhen.AddOperand(gpBefore);
                cfWhen.AddOperand(gpAfter);
                cfAnd.AddOperand(cfWhen);
            }
            a.Effects = cfAnd.Simplify();
        }

        private List<PlanningAction> AddMishapIncreaseNonConditional(PlanningAction a, int cMishaps)
        {
            List<PlanningAction> lActions = new List<PlanningAction>();
            for (int i = 0; i < cMishaps; i++)
            {
                PlanningAction aMishap = a.Clone();
                aMishap.Name += i;
                CompoundFormula cfPre = new CompoundFormula("and");
                cfPre.AddOperand(a.Preconditions);
                CompoundFormula cfEffects = new CompoundFormula("and");
                cfEffects.AddOperand(a.Effects);
                GroundedPredicate gpBefore = new GroundedPredicate("MishapCount");
                gpBefore.AddConstant(new Constant("mishaps", "m" + i));
                cfPre.AddOperand(gpBefore);
                GroundedPredicate gpAfter = new GroundedPredicate("MishapCount");
                gpAfter.AddConstant(new Constant("mishaps", "m" + (i + 1)));
                cfEffects.AddOperand(gpAfter);

                aMishap.Preconditions = cfPre.Simplify();
                aMishap.Effects = cfEffects.Simplify();
                lActions.Add(aMishap);
            }
            return lActions;
        }
        private void WriteAction(StreamWriter sw, PlanningAction a, List<Formula> lDeadends)
        {
            WriteAction(sw, a, false, lDeadends);
        }

        private void WriteAction(StreamWriter sw, PlanningAction a, bool bInitPrecondition, List<Formula> lDeadends)
        {
            if (Options.RemoveConflictingConditionalEffects)
                RemoveConflictingConditionalEffectsFromAction(a);

            sw.WriteLine("(:action " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(a.Preconditions);
                if (bInitPrecondition)
                    cfAnd.AddOperand(new GroundedPredicate("not-init"));
                if (lDeadends != null)
                {
                    foreach (Formula f in lDeadends)
                    {
                        if (f is PredicateFormula)
                            cfAnd.AddOperand(f.Negate());
                        else
                        {
                            // if deadend is (p & q) the negated formula is complex - better not use it
                            //foreach(Formula fSub in ((CompoundFormula)f).Operands)
                            //    cfAnd.AddOperand(fSub.Negate());
                        }
                    }
                }
                sw.WriteLine(":precondition " + cfAnd);
            }
            if (a.Effects != null)
                sw.WriteLine(":effect " + a.Effects);
            if (a.Observe != null)
                sw.WriteLine(":observe " + a.Observe);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        private void WriteSensor(StreamWriter sw, PlanningAction a)
        {
            Debug.Assert(a.Observe != null && a.Effects == null);
            sw.WriteLine("(:sensor " + a.Name);
            if (a is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)a;
                sw.Write(":parameters (");
                foreach (Parameter p in pa.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (a.Preconditions != null)
                sw.WriteLine(":condition " + a.Preconditions);
            sw.WriteLine(":sensed " + a.Observe);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        public List<PlanningAction> GetAllKnowledgeActions(Dictionary<string, List<Predicate>> dTags)
        {
            List<PlanningAction> lActions = new List<PlanningAction>();
            foreach (PlanningAction a in Actions)
            {
                if (a.Effects == null & a.Observe != null)
                {
                    PlanningAction aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    lActions.Add(aObserveTrue);
                    PlanningAction aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lActions.Add(aObserveFalse);
                }

                else
                {
                    PlanningAction aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    lActions.Add(aKnowledge);
                }
            }
            return lActions;
        }

        private List<PlanningAction> GetKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<PlanningAction> lAllActions = new List<PlanningAction>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (PlanningAction a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<PlanningAction> lKnowWhether = a.TagObservationTranslationNoState(dTags, this);
                    lAllActions.AddRange(lKnowWhether);
                }
                else
                {
                    List<PlanningAction> lKnowWhether = a.TagCompilationNoState(dTags, this, lAdditionalPredicates);
                    lAllActions.AddRange(lKnowWhether);
                }
            }
            return lAllActions;
        }



        private List<PlanningAction> GetKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Predicate> lAdditionalPredicates)
        {
            List<PlanningAction> lAllActions = new List<PlanningAction>();
            lAdditionalPredicates.Add(new GroundedPredicate("NotInAction"));

            foreach (PlanningAction a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    PlanningAction aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    PlanningAction aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    lAllActions.Add(aObserveTrue);
                    lAllActions.Add(aObserveFalse);
                }
                else
                {
                    List<PlanningAction> lCompiled = a.KnowCompilationSplitConditions(dTags, m_lAlwaysKnown, lAdditionalPredicates);
                    lAllActions.AddRange(lCompiled);
                }
            }
            return lAllActions;
        }



        private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            int cTranslatedActions = 0;
            foreach (PlanningAction a in Actions)
            {
                if (a.Effects == null && a.Observe != null)
                {
                    List<PlanningAction> lCompiled = a.TagObservationTranslationNoState(dTags, this);
                    foreach (PlanningAction aKnowWhether in lCompiled)
                        WriteConditionalAction(sw, aKnowWhether, null);
                }
                else
                {
                    List<PlanningAction> lCompiled = a.TagCompilationNoState(dTags, this, null);
                    foreach (PlanningAction aCompiled in lCompiled)
                    {
                        //Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + "Writing action " + aCompiled.Name + " : " + cTranslatedActions);
                        cTranslatedActions++;
                        WriteConditionalAction(sw, aCompiled, null);
                    }
                    //Debug.WriteLine("");
                }
            }
        }


        /*
                private void WriteKnowledgeActionsNoState(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
                {
                    int  cTranslatedActions = 0;
                    int cMaxTranslatedConditionalEffects = 0, cMaxOriginalConditionalEffects = 0;
                    foreach (Action a in Actions)
                    {
                        //if (a.GetConditions().Count > cMaxOriginalConditionalEffects)
                        //    cMaxOriginalConditionalEffects = a.GetConditions().Count;


                        if (a.Effects == null && a.Observe != null)
                        {
                            //Action aKnow = a.KnowObservationTranslation();
                            //WriteConditionalAction(sw, aKnow);
                            BUGBUG;
                            List<Action> lKnowWhether = a.KnowWhetherTagObservationTranslation(dTags, this);
                            foreach (Action aKnowWhether in lKnowWhether)
                                WriteConditionalAction(sw, aKnowWhether);
                        }
                        else
                        {
                            //Action aKnow = a.KnowCompilation(dTags, this);
                            //WriteConditionalAction(sw, aKnow);
                            List<Action> lKnowWhether = a.KnowWhetherTagCompilation(dTags, this);
                            foreach (Action aKnowWhether in lKnowWhether)
                            {
                                cTranslatedActions++;
                                //if (aKnowWhether.GetConditions().Count > cMaxTranslatedConditionalEffects)
                                //    cMaxTranslatedConditionalEffects = aKnowWhether.GetConditions().Count;
                                WriteConditionalAction(sw, aKnowWhether);
                            }
                        }
                    }
                    //Debug.WriteLine("Original: #Actions " + Actions.Count + ", Max conditions " + cMaxOriginalConditionalEffects);
                    //Debug.WriteLine("Translated: #Actions " + cTranslatedActions + ", Max conditions " + cMaxTranslatedConditionalEffects);
                }
        */

        private void WriteKnowledgeActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, List<Formula> lDeadends)
        {
            foreach (PlanningAction a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (Options.ReplaceNonDeterministicEffectsWithOptions)
                    {
                        PlanningAction aDeterministic = a.ReplaceNonDeterministicEffectsWithOptions(m_lAlwaysKnown);
                        PlanningAction aKnowledge = aDeterministic.AddTaggedConditions(dTags, m_lAlwaysKnown);
                        WriteConditionalAction(sw, aKnowledge, lDeadends);
                    }
                    else
                    {
                        List<PlanningAction> lKnowledgeActions = a.AddTaggedNonDeterministicConditions(dTags, m_lAlwaysKnown);
                        foreach (PlanningAction aKnowledge in lKnowledgeActions)
                            WriteConditionalAction(sw, aKnowledge, lDeadends);
                    }
                }

                else if (a.Effects == null && a.Observe != null)
                {
                    PlanningAction aObserveTrue = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, true);
                    aObserveTrue.AddEffect(Utilities.Observed);
                    WriteConditionalAction(sw, aObserveTrue, lDeadends);
                    PlanningAction aObserveFalse = a.NonConditionalObservationTranslation(dTags, m_lAlwaysKnown, false);
                    aObserveFalse.AddEffect(Utilities.Observed);
                    WriteConditionalAction(sw, aObserveFalse, lDeadends);
                }

                else
                {
                    PlanningAction aKnowledge = a.AddTaggedConditions(dTags, m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge, lDeadends);
                }
                /* I can't split the effects like that becuase if KC/t -> KE/t even if C is not true
                if (a.HasConditionalEffects)
                {
                    List<Action> aSplitted = a.SplitTaggedConditions(dTags, m_lAlwaysKnown);
                    foreach (Action aKnowledge in aSplitted)
                        WriteConditionalAction(sw, aKnowledge);
                }
                else
                {
                    Action aKnowledge = a.AddKnowledge(m_lAlwaysKnown);
                    WriteConditionalAction(sw, aKnowledge);
                }
                 * */
            }
        }

        private void WriteReasoningActions(StreamWriter sw, Dictionary<string, List<Predicate>> dTags, Problem pCurrent, List<Formula> lDeadends)
        {
            //write merges andUtilities.TAG refutation
            foreach (Predicate p in Predicates)
            {
                if (p is ParametrizedPredicate)
                {
                    ParametrizedPredicate pp = (ParametrizedPredicate)p;
                    if (!AlwaysKnown(pp))
                    {
                        PlanningAction aMergeTrue = GenerateMergeAction(pp, dTags, true);
                        aMergeTrue.AddPrecondition(Utilities.Observed);
                        WriteAction(sw, aMergeTrue, lDeadends);
                        PlanningAction aMergeFalse = GenerateMergeAction(pp, dTags, false);
                        aMergeFalse.AddPrecondition(Utilities.Observed);
                        WriteAction(sw, aMergeFalse, lDeadends);
                        PlanningAction aRefute = GenerateRefutationAction(pp, true);
                        aRefute.AddPrecondition(Utilities.Observed);
                        WriteAction(sw, aRefute, lDeadends);
                        aRefute = GenerateRefutationAction(pp, false);
                        aRefute.AddPrecondition(Utilities.Observed);
                        WriteAction(sw, aRefute, lDeadends);

                        //Action aAssert = GenerateAssertInvalid(pp, pCurrent.Goal);
                        //WriteAction(sw, aAssert);
                    }
                }
            }
        }
        private bool Observable(ParametrizedPredicate pp)
        {
            foreach (PlanningAction a in Actions)
            {
                if (a.Observe != null)
                {
                    HashSet<Predicate> lObservables = a.Observe.GetAllPredicates();
                    foreach (Predicate p in lObservables)
                    {
                        if (p.Name == pp.Name)
                            return true;
                    }

                }
            }
            return false;
        }

        private PlanningAction GenerateTagMergeAction(ParametrizedPredicate pp, List<string> lIncludedTags, List<string> lExcludedTags, bool bValue)
        {
            string sName = "TagMerge-" + pp.Name;
            foreach (string sTag in lIncludedTags)
                sName += "-" + sTag;
            if (bValue == true)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");

            foreach (string sTag in lIncludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == Utilities.VALUE)
                        p.Name = Utilities.VALUE_PARAMETER;

                if (bValue == true)
                    cfAnd.AddOperand(ppKGivenT);
                else
                    cfAnd.AddOperand(ppKGivenT.Negate());

                if (sTag != lIncludedTags[0])
                {
                    Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, sTag), new Constant(Utilities.TAG, lIncludedTags[0]));
                    cfAnd.AddOperand(pKNotT.Negate());
                }
            }
            foreach (string sTag in lExcludedTags)
            {
                ParametrizedPredicate ppKGivenT = (ParametrizedPredicate)pp.GenerateGiven(sTag);
                foreach (Parameter p in ppKGivenT.Parameters)
                    if (p.Type == Utilities.VALUE)
                        p.Name = Utilities.VALUE_PARAMETER;
                Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, sTag), new Constant(Utilities.TAG, lIncludedTags[0]));
                cfAnd.AddOperand(pKNotT);
            }
            if (Options.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            foreach (string sTag in lIncludedTags)
            {
                Predicate ppK = pp.GenerateKnowGiven(sTag, true);
                cfAnd.AddOperand(ppK);
            }

            pa.SetEffects(cfAnd);
            return pa;
        }

        private PlanningAction GenerateMergeActionBUGBUG(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags)
        {
            ParametrizedAction pa = new ParametrizedAction("Merge-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            Parameter pValue = new Parameter(Utilities.VALUE, Utilities.VALUE_PARAMETER);
            pa.AddParameter(pValue);
            CompoundFormula cfAnd = new CompoundFormula("and");

            KnowPredicate ppK = new KnowPredicate(pp);
            ppK.Parametrized = true;
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p

            if (Options.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
                Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(Utilities.TAG, sTag));
                ppKGivenT.AddParameter(pValue);
                cfOr.AddOperand(new PredicateFormula(ppKGivenT));
                cfOr.AddOperand(new PredicateFormula(pKNotT));
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;

            throw new Exception("BUGBUG: if value is false for both cases, we still get true - not good");

            cfAnd.AddOperand(ppK);
            pa.SetEffects(cfAnd);
            return pa;
        }
        private PlanningAction GenerateMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bTrue)
        {
            BUGBUG;//move from (not (Kp)) (not (KNp)) to Up (for unknown p) - also in sensing actions
            string sName = "Merge-" + pp.Name + "-";
            if (bTrue)
                sName += "T";
            else
                sName += "F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
            {
                CPORPlanner.TraceListener.WriteLine(sName + ":" + param.Name);
                pa.AddParameter(param);
            }
            CompoundFormula cfAnd = new CompoundFormula("and");

            KnowPredicate ppK = new KnowPredicate(pp);
            KnowPredicate ppNK = new KnowPredicate(pp.Negate());
            
            ppK.Parametrized = true;
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p
            cfAnd.AddOperand(ppNK.Negate());//add ~know ~p to the preconditions - no point in activating merge when we know p

            if (Options.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));

            foreach (string sTag in dTags.Keys)
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
                Predicate pKNotT = Predicate.GenerateKNot(new Constant(Utilities.TAG, sTag));
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(Utilities.TAG, sTag));
                if(bTrue)
                    ppKGivenT.AddParameter(new Constant(Utilities.VALUE_PARAMETER, Utilities.TRUE_VALUE) );
                else
                    ppKGivenT.AddParameter(new Constant(Utilities.VALUE_PARAMETER, Utilities.FALSE_VALUE));
                cfOr.AddOperand(new PredicateFormula(ppKGivenT));
                cfOr.AddOperand(new PredicateFormula(pKNotT));
                cfAnd.AddOperand(cfOr);
            }
            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            if (bTrue)
                cfAnd.AddOperand(ppK);
            else
                cfAnd.AddOperand(ppNK);
            pa.SetEffects(cfAnd);
            return pa;
        }


        private PlanningAction GenerateKnowMergeAction(ParametrizedPredicate pp, Domain d, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            string sName = "";
            if (bKnowWhether)
            {
                sName = "Merge-KW-" + pp.Name;
            }
            else
            {
                sName = "Merge-K-" + pp.Name;
                if (bValue == true)
                    sName += "-T";
                else
                    sName += "-F";
            }
            pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            cfAnd.AddOperand(ppK.Negate());//add ~know p to the preconditions - no point in activating merge when we know p
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                {
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                }
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(Utilities.TAG, sTag));
                if (!bKnowWhether && bValue == false)
                    cfAnd.AddOperand(ppKGivenT.Negate());
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.Preconditions = cfAnd;
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            if (!bKnowWhether && !d.AlwaysKnown(pp))
                cfAnd.AddOperand(new KnowWhetherPredicate(pp));
            pa.SetEffects(cfAnd);
            return pa;
        }

        private PlanningAction GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue, bool bKnowWhether)
        {
            ParametrizedAction pa = null;
            if (bKnowWhether)
                pa = new ParametrizedAction("UnMerge-KW-" + pp.Name);
            else
                pa = new ParametrizedAction("UnMerge-K-" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = null;
            if (bKnowWhether)
            {
                ppK = new KnowWhetherPredicate(pp);
            }
            else
            {
                ppK = new KnowPredicate(pp, bValue, false);
            }
            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = null;
                if (bKnowWhether)
                    ppKGivenT = new ParametrizedPredicate("KWGiven" + pp.Name);
                else
                    ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(Utilities.TAG, sTag));
                if (!bKnowWhether && bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects(cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private PlanningAction GenerateKnowUnMergeAction(ParametrizedPredicate pp, Dictionary<string, List<Predicate>> dTags, bool bValue)
        {
            string sName = "UnMerge-K-" + pp.Name;
            if (bValue)
                sName += "-T";
            else
                sName += "-F";
            ParametrizedAction pa = new ParametrizedAction(sName);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);

            CompoundFormula cfAnd = new CompoundFormula("and");
            Predicate ppK = new KnowPredicate(pp, bValue, false);

            foreach (string sTag in dTags.Keys)
            {
                ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("Given" + pp.Name);
                foreach (Parameter param in pp.Parameters)
                    ppKGivenT.AddParameter(param);
                ppKGivenT.AddParameter(new Constant(Utilities.TAG, sTag));
                if (bValue == false)
                {
                    cfAnd.AddOperand(ppKGivenT.Negate());
                }
                else
                    cfAnd.AddOperand(ppKGivenT);
            }
            pa.SetEffects(cfAnd);
            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(ppK);
            pa.Preconditions = cfAnd;
            return pa;
        }

        private PlanningAction GenerateRefutationAction(ParametrizedPredicate pp, bool bValue)
        {
            string sName = "Refute";
            if (bValue)
                sName += "T";
            else
                sName += "F";
            sName += "-" + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(Utilities.TAG, Utilities.TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
            {
                CPORPlanner.TraceListener.WriteLine(sName + ":" + param.Name);
                pa.AddParameter(param);
            }
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            if (bValue)
                ppKGivenT.AddParameter(new Constant(Utilities.VALUE, Utilities.TRUE_VALUE));
            else
                ppKGivenT.AddParameter(new Constant(Utilities.VALUE, Utilities.FALSE_VALUE));

            Predicate pKNotT = Predicate.GenerateKNot(pTag);
            cfAnd.AddOperand(pKNotT.Negate());//add ~know not t - if we already know that t is false there is no point in runningUtilities.TAG refutation

            if (Options.SplitConditionalEffects)
                cfAnd.AddOperand(new GroundedPredicate("NotInAction"));


            KnowPredicate ppK = new KnowPredicate(pp, !bValue, false);
            cfAnd.AddOperand(ppKGivenT);
            cfAnd.AddOperand(ppK);

            if (bValue)
                cfAnd.AddOperand(pp.Negate());
            else
                cfAnd.AddOperand(pp);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(new PredicateFormula(pKNotT));
            pa.SetEffects(cfAnd);
            return pa;
        }


        private PlanningAction GenerateAssertInvalid(ParametrizedPredicate pp, Formula fGoal)
        {
            string sName = "AssertInvalid";
            sName += Utilities.DELIMITER_CHAR + pp.Name;
            ParametrizedAction pa = new ParametrizedAction(sName);
            Parameter pTag = new Parameter(Utilities.TAG, Utilities.TAG_PARAMETER);
            foreach (Parameter param in pp.Parameters)
                pa.AddParameter(param);
            pa.AddParameter(pTag);
            CompoundFormula cfAnd = new CompoundFormula("and");
            ParametrizedPredicate ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Utilities.VALUE, Utilities.TRUE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            ppKGivenT = new ParametrizedPredicate("KGiven" + pp.Name);
            foreach (Parameter param in pp.Parameters)
                ppKGivenT.AddParameter(param);
            ppKGivenT.AddParameter(pTag);
            ppKGivenT.AddParameter(new Parameter(Utilities.VALUE, Utilities.FALSE_VALUE));
            cfAnd.AddOperand(ppKGivenT);

            pa.Preconditions = cfAnd;

            cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(fGoal);

            HashSet<Predicate> lAllGoal = fGoal.GetAllPredicates();
            foreach (Predicate p in lAllGoal)
            {
                if (!AlwaysKnown(p))
                    cfAnd.AddOperand(new KnowPredicate(p));
            }

            pa.SetEffects(cfAnd);
            return pa;
        }


        private void WriteKnowledgeActions(StreamWriter sw, int cMinMishaps, int cMishaps, bool bMishapType, bool bRequireP)
        {
            foreach (PlanningAction a in Actions)
            {
                List<PlanningAction> lNoConditionalEffects = RemoveConditionalEffects(a);

                foreach (PlanningAction aNonConditional in lNoConditionalEffects)
                {
                    List<PlanningAction> lDeterministic = a.RemoveNonDeterministicEffects();
                    foreach (PlanningAction aDet in lDeterministic)
                        WriteKnowledgeAction(sw, aDet, cMinMishaps, cMishaps, bMishapType, bRequireP);
                }

            }
        }

        private List<PlanningAction> RemoveConditionalEffects(PlanningAction a)
        {
            List<PlanningAction> lActions = new List<PlanningAction>();
            if (!a.ContainsNonDeterministicEffect || !a.HasConditionalEffects)//  || Utilities.Planner != Utilities.Planners.CPT))
            {
                lActions.Add(a);
                return lActions;
            }
            HashSet<Predicate> lMandatoryEffects = a.GetMandatoryEffects();
            List<CompoundFormula> lConditions = a.GetConditions();

            //if (lConditions.Count > 1)
            //   throw new NotImplementedException();

            foreach (CompoundFormula cfWhen in lConditions)
            {
                PlanningAction aWithCondition = a.Clone();
                CompoundFormula cfPreconditions = new CompoundFormula("and");
                cfPreconditions.AddOperand(a.Preconditions);
                cfPreconditions.AddOperand(cfWhen.Operands[0]);
                aWithCondition.Preconditions = cfPreconditions.Simplify();
                CompoundFormula cfEffects = new CompoundFormula("and");
                foreach (Predicate p in lMandatoryEffects)
                    cfEffects.AddOperand(p);
                cfEffects.AddOperand(cfWhen.Operands[1]);
                aWithCondition.Effects = cfEffects;
                lActions.Add(aWithCondition);

                if (lMandatoryEffects.Count > 0)
                {
                    //this is not quite true, because we need to add (not p) to the preconditions, but CPT dislikes negative preconditions
                    PlanningAction aWithoutCondition = a.Clone();
                    cfEffects = new CompoundFormula("and");
                    foreach (Predicate p in lMandatoryEffects)
                        cfEffects.AddOperand(p);
                    aWithoutCondition.Effects = cfEffects;
                    lActions.Add(aWithoutCondition);
                }

            }
            return lActions;
        }

        private void RemoveConflictingConditionalEffectsFromAction(PlanningAction a)
        {
            CompoundFormula cfPreconditions = null;
            if (a.Preconditions == null)
            {
                cfPreconditions = new CompoundFormula("and");
                a.Preconditions = cfPreconditions;
            }
            else if (a.Preconditions is PredicateFormula)
            {
                cfPreconditions = new CompoundFormula("and");
                cfPreconditions.AddOperand(a.Preconditions);
                a.Preconditions = cfPreconditions;
            }
            else
            {
                cfPreconditions = (CompoundFormula)a.Preconditions;
            }
            cfPreconditions.AddOperand(new GroundedPredicate("axioms-applied"));

            CompoundFormula cfEffects = new CompoundFormula("and");
            cfEffects.AddOperand(new GroundedPredicate("axioms-applied").Negate());
            if (a.Effects is PredicateFormula)
            {
                cfEffects.AddOperand(a.Effects);
                a.SetEffects(cfEffects);
            }
            else
            {
                CompoundFormula cfOldEffects = (CompoundFormula)a.Effects;
                foreach (Formula f in cfOldEffects.Operands)
                {
                    if (f is PredicateFormula)
                        cfEffects.AddOperand(f);
                    else
                        cfEffects.AddOperand(((CompoundFormula)f).ReplaceNegativeEffectsInCondition());

                }
            }
            a.SetEffects(cfEffects);
        }

        private void WriteConditionalAction(StreamWriter sw, PlanningAction aKnowledge, List<Formula> lDeadends)
        {
            sw.WriteLine("(:action " + aKnowledge.Name);
            if (aKnowledge is ParametrizedAction)
            {
                ParametrizedAction pa = (ParametrizedAction)aKnowledge;
                sw.Write(":parameters (");
                foreach (Parameter param in pa.Parameters)
                    sw.Write(" " + param.Name + " - " + param.Type);
                sw.WriteLine(")");
            }
            if (Options.RemoveConflictingConditionalEffects)
            {
                RemoveConflictingConditionalEffectsFromAction(aKnowledge);
            }


            if (aKnowledge.Preconditions != null)
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                cfAnd.AddOperand(aKnowledge.Preconditions);
                if (lDeadends != null)
                {
                    foreach (Formula f in lDeadends)
                    {
                        if (f is PredicateFormula)
                            cfAnd.AddOperand(f.Negate());
                        else
                        {
                            // if deadend is (p & q) the negated formula is complex - better not use it
                            //foreach(Formula fSub in ((CompoundFormula)f).Operands)
                            //    cfAnd.AddOperand(fSub.Negate());
                        }
                    }
                }
                sw.WriteLine(":precondition " + cfAnd);
            }
            sw.WriteLine(":effect " + aKnowledge.Effects.ToString().Replace("(when", "\n\t(when"));
            sw.WriteLine(")");
        }
        /* using KW predicates
        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                /*
                if (pp.Name != Utilities.OPTION_PREDICATE)
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.VALUE_PARAMETER + " - " +Utilities.VALUE);
                    sw.WriteLine(")");
                }
                 * *
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.VALUE_PARAMETER + " - " +Utilities.VALUE);
                    sw.WriteLine(")");
                }
                if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                {
                    /*
                    sw.Write("(KGiven" + pp.Name);//write know-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.TAG_PARAMETER + " - " +Utilities.TAG);
                    sw.Write(" " + Utilities.VALUE_PARAMETER + " - " +Utilities.VALUE);
                    sw.WriteLine(")");
                     * *
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.TAG_PARAMETER + " - " +Utilities.TAG);
                    sw.WriteLine(")");
                }
                if (!AlwaysKnown(pp) && pp.Name != Utilities.OPTION_PREDICATE)
                {
                    /*
                    sw.Write("(KW" + pp.Name);//write know-whether predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    *
                    //maybe we can further remove this for constant predicates? Not sure.
                    sw.Write("(KWGiven" + pp.Name);//write know-whether-given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.TAG_PARAMETER + " - " +Utilities.TAG);
                    sw.WriteLine(")");
                }
            }

            sw.WriteLine("(KNot " + Utilities.TAG_PARAMETER + "1 - " +Utilities.TAG + " " + Utilities.TAG_PARAMETER + "2 - " +Utilities.TAG + ")");//forUtilities.TAG refutation

            for (int iTime = 0; iTime < Options.TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }
*/

        private void WriteTaggedPredicatesNoState(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");
            if (lAdditinalPredicates == null)
                sw.WriteLine("(NotInAction)");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (AlwaysConstant(pp) && AlwaysKnown(pp))
                {
                    sw.Write("(" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }
                //if (!AlwaysConstant(pp) || !AlwaysKnown(pp))
                else
                {
                    sw.Write("(Given" + pp.Name);//write given predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                    sw.WriteLine(")");
                    if (Options.SplitConditionalEffects)
                    {
                        sw.Write("(Given" + pp.Name + "-Add");//write givenp-add predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                        sw.WriteLine(")");
                        sw.Write("(Given" + pp.Name + "-Remove");//write givenp-remove predicate
                        foreach (Parameter p in pp.Parameters)
                            sw.Write(" " + p.FullString());
                        sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                        sw.WriteLine(")");
                    }
                }
            }

            sw.WriteLine("(KNot " + Utilities.TAG_PARAMETER + "1 - " + Utilities.TAG + " " + Utilities.TAG_PARAMETER + "2 - " + Utilities.TAG + ")");//forUtilities.TAG distinguishability 

            for (int iTime = 0; iTime < Options.TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }


        private void WriteTaggedPredicates(StreamWriter sw, List<Predicate> lAdditinalPredicates)
        {
            sw.WriteLine("(:predicates");

            sw.WriteLine(Utilities.Observed);

            foreach (Predicate p in Predicates)
            {
                List<Argument> Params = new List<Argument>();
                if (p is ParametrizedPredicate)
                    Params = new List<Argument>(((ParametrizedPredicate)p).Parameters);
                sw.Write("(" + p.Name);//write regular predicate
                foreach (Parameter param in Params)
                    sw.Write(" " + param.FullString());
                sw.WriteLine(")");


                if (Options.RemoveConflictingConditionalEffects)
                {
                    sw.Write("(Not-" + p.Name);//write regular predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.WriteLine(")");
                }

                if (Options.SplitConditionalEffects)
                {
                    sw.Write("(" + p.Name + "-Add");//write regular predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.WriteLine(")");
                    sw.Write("(" + p.Name + "-Remove");//write regular predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.WriteLine(")");
                }

                if (!AlwaysKnown(p))
                {
                    /*
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.Write(" " + Utilities.VALUE_PARAMETER + " - " +Utilities.VALUE);
                    sw.WriteLine(")");
                    */
                    sw.Write("(K" + p.Name);//write know predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.WriteLine(")");
                    sw.Write("(KN" + p.Name);//write know predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.WriteLine(")");


                    if (Options.RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-K" + p.Name);//write regular predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                    }

                    if (Options.SplitConditionalEffects)
                    {
                        sw.Write("(K" + p.Name + "-Add");//write know predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                        sw.Write("(K" + p.Name + "-Remove");//write know predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                    }

                    sw.Write("(KGiven" + p.Name);//write know-given predicate
                    foreach (Parameter param in Params)
                        sw.Write(" " + param.FullString());
                    sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                    sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                    sw.WriteLine(")");

                    if (Options.RemoveConflictingConditionalEffects)
                    {
                        sw.Write("(Not-KGiven" + p.Name);//write regular predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                    }

                    if (Options.SplitConditionalEffects)
                    {
                        sw.Write("(KGiven" + p.Name + "-Add");//write know-given predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                        sw.Write("(KGiven" + p.Name + "-Remove");//write know-given predicate
                        foreach (Parameter param in Params)
                            sw.Write(" " + param.FullString());
                        sw.Write(" " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG);
                        sw.Write(" " + Utilities.VALUE_PARAMETER + " - " + Utilities.VALUE);
                        sw.WriteLine(")");
                    }
                }
            }
            sw.WriteLine("(KNot " + Utilities.TAG_PARAMETER + " - " + Utilities.TAG + ")");//forUtilities.TAG refutation

            if (Options.RemoveConflictingConditionalEffects)
            {
                sw.WriteLine("(axioms-applied)");
                HashSet<GroundedPredicate> lGrounded = GroundAllPredicates();
                foreach (GroundedPredicate gp in lGrounded)
                {
                    sw.Write("(axioms-applied-" + gp.Name);
                    foreach (Constant c in gp.Constants)
                        sw.Write("-" + c.Name);
                    sw.WriteLine(")");
                }

            }
            /*
            if (Options.UseOptions)
            {
                sw.WriteLine("(Utilities.OPTION ?x - " + OPTION + ")");
            }
            */
            for (int iTime = 0; iTime < Options.TIME_STEPS; iTime++)
                sw.WriteLine("(time" + iTime + ")");

            if (lAdditinalPredicates != null)
            {
                foreach (Predicate p in lAdditinalPredicates)
                    sw.WriteLine(p);
            }
            sw.WriteLine(")");
        }

        private void WriteKnowledgePredicates(StreamWriter sw, int cMinMishaps, int cMishaps, bool bRequireP)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                if (AlwaysKnown(pp) || bRequireP)
                {
                    sw.Write("(" + pp.Name);//write regular predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                }
                if (!AlwaysKnown(pp))
                {
                    sw.Write("(K" + pp.Name);//write know predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    sw.Write("(KN" + pp.Name);//write know not predicate
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    /*
                    sw.Write("(NotK" + pp.Name);//write not know predicate - for planners that ignore negative preconditions
                    foreach (Parameter p in pp.Parameters)
                        sw.Write(" " + p.FullString());
                    sw.WriteLine(")");
                    */
                }
            }
            if (cMinMishaps > cMishaps)
            {
                sw.WriteLine("(MishapCount ?m - mishaps)");
            }
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw, int cMinMishaps, int cMishaps)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            if (cMinMishaps > cMishaps)
            {
                for (int i = 0; i <= cMinMishaps; i++)
                {
                    sw.Write(" m" + i);

                }
                sw.WriteLine(" - mishaps");
            }
            sw.WriteLine(")");
        }

        private void WriteConstants(StreamWriter sw, Dictionary<string, List<Predicate>> dTags)
        {
            sw.WriteLine("(:constants");
            foreach (Constant c in Constants)
                sw.WriteLine(" " + c.FullString());
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {
                sw.Write(" " + p.Key + " - " + Utilities.TAG + " ;");
                foreach (Predicate pred in p.Value)
                {
                    sw.Write(" " + pred.ToString());
                }
                sw.WriteLine();
            }
            sw.WriteLine(" " + Utilities.TRUE_VALUE + " - " + Utilities.VALUE);
            sw.WriteLine(" " + Utilities.FALSE_VALUE + " - " + Utilities.VALUE);
            /*
            if (Options.UseOptions && HasNonDeterministicActions())
            {
                int cOptions = MaxNonDeterministicEffects();
                for( int i = 0 ; i < cOptions ; i++ )
                    sw.Write(" " + "opt" + i + " - " + OPTION);
                sw.WriteLine();
            }
             * */
            sw.WriteLine(")");
        }

        private void WriteTypes(StreamWriter sw, bool bUseTags)
        {
            sw.WriteLine("(:types");
            if (TypeHierarchy.Count == 0)
            {
                foreach (string sType in Types)
                    sw.Write(" " + sType);
            }
            else
            {
                foreach (KeyValuePair<string, string> p in TypeHierarchy)
                {
                    sw.WriteLine("\t" + p.Key + " - " + p.Value);
                }
            }
            if (bUseTags)
            {
                sw.Write(" " + Utilities.TAG);
                sw.Write(" " + Utilities.VALUE);
            }
            /*
            if (Options.UseOptions && HasNonDeterministicActions())
            {
                sw.Write(" " + OPTION);
            }
             * */
            sw.WriteLine("\n)");
        }

        public bool HasNonDeterministicActions()
        {
            foreach (PlanningAction a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                    return true;
            }
            return false;
        }

        public int MaxNonDeterministicEffects()
        {
            int cMaxOptions = 0;
            foreach (PlanningAction a in Actions)
            {
                if (a.ContainsNonDeterministicEffect)
                {
                    if (a.Effects.GetMaxNonDeterministicOptions() > cMaxOptions)
                        cMaxOptions = a.Effects.GetMaxNonDeterministicOptions();
                }
            }
            return cMaxOptions;
        }

        private PlanningAction GetActionByName(string sActionName)
        {
            foreach (PlanningAction a in Actions)
            {
                if (a.Name.ToLower() == sActionName.ToLower())
                {
                    return a;
                }
                if (a.Name.ToLower().Replace(Utilities.DELIMITER_CHAR, "-") == sActionName)
                    return a;
            }
            PlanningAction aBestMatch = null;
            foreach (PlanningAction a in Actions)
            {
                if (sActionName.StartsWith(a.Name.ToLower())) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
                if (sActionName.StartsWith(a.Name.ToLower().Replace(Utilities.DELIMITER_CHAR, "-"))) //assuming that this is a splitted conditional effect action. BUGBUG - need better solution for this
                {
                    if (aBestMatch == null || aBestMatch.Name.Length < a.Name.Length)
                        aBestMatch = a;
                }
            }
            return aBestMatch;
        }
        private Dictionary<Parameter, Constant> GetBindings(ParametrizedAction pa, string[] asAction)
        {
            if (pa.Parameters.Count > asAction.Length - 1)//last parameter can be theUtilities.TAG of a KW action
                return null;
            Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
            for (int iParameter = 0; iParameter < pa.Parameters.Count; iParameter++)
            {
                dBindings[pa.Parameters[iParameter]] = new Constant(pa.Parameters[iParameter].Type, asAction[iParameter + 1]);
            }
            return dBindings;
        }
        public PlanningAction GroundActionByName(string[] asAction, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            string sActionName = asAction[0];
            PlanningAction a = GetActionByName(sActionName);
            if (!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;
            Dictionary<Parameter, Constant> dBindings = GetBindings(pa, asAction);

            Formula fGroundedPreconditions = null;
            if (pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            if (pa.Preconditions == null || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
            {
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += Utilities.DELIMITER_CHAR + dBindings[p].Name;
                PlanningAction aGrounded = new PlanningAction(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                return aGrounded;
            }
            return null;
        }

        public PlanningAction GroundActionByName(string[] asAction)
        {
            string sActionName = asAction[0];
            PlanningAction a = GetActionByName(sActionName);
            if (!(a is ParametrizedAction))
                return a;
            ParametrizedAction pa = (ParametrizedAction)a;
            Dictionary<Parameter, Constant> dBindings = GetBindings(pa, asAction);

            if (dBindings == null)
                return null;

            Formula fGroundedPreconditions = null;
            if (pa.Preconditions != null)
                fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
            else if (pa.Effects != null)
                pa.Effects.Ground(dBindings);
            else if (pa.Observe != null)
                pa.Observe.Ground(dBindings);
            string sName = pa.Name;
            foreach (Parameter p in pa.Parameters)
                sName += Utilities.DELIMITER_CHAR + dBindings[p].Name;
            PlanningAction aGrounded = new PlanningAction(sName);
            aGrounded.Preconditions = fGroundedPreconditions;
            if (pa.Effects != null)
            {
                aGrounded.SetEffects(pa.Effects.Ground(dBindings));

            }
            if (pa.Observe != null)
                aGrounded.Observe = pa.Observe.Ground(dBindings);
            return aGrounded;
        }

        public void GroundPredicate(ParametrizedPredicate pp, Dictionary<Parameter, Constant> dBindings, List<Argument> lRemaining, HashSet<GroundedPredicate> lGrounded)
        {
            if (lRemaining.Count == 0)
            {
                GroundedPredicate gp = new GroundedPredicate(pp.Name);
                foreach (Parameter p in pp.Parameters)
                    gp.AddConstant(dBindings[p]);
                lGrounded.Add(gp);
            }
            else
            {
                Argument a = lRemaining[0];
                List<Argument> lNewRemaining = new List<Argument>(lRemaining);
                lNewRemaining.RemoveAt(0);
                if (a is Parameter)
                {
                    Parameter p = (Parameter)a;
                    foreach (Constant c in Constants)
                    {
                        if (p.Type == "" || ParentOf(p.Type, c.Type))
                        {
                            dBindings[p] = c;
                            GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                        }
                    }
                }
                else
                {
                    GroundPredicate(pp, dBindings, lNewRemaining, lGrounded);
                }
            }
        }
        public HashSet<GroundedPredicate> GroundAllPredicates()
        {
            HashSet<string> lExcludePredicateNames = new HashSet<string>();
            return GroundAllPredicates(lExcludePredicateNames);
        }
        public HashSet<GroundedPredicate> GroundAllPredicates(HashSet<string> lExcludePredicateNames)
        {
            HashSet<GroundedPredicate> lGrounded = new HashSet<GroundedPredicate>();
            foreach (Predicate p in Predicates)
            {
                if (!lExcludePredicateNames.Contains(p.Name))
                {
                    if (p is ParametrizedPredicate)
                    {
                        ParametrizedPredicate pp = (ParametrizedPredicate)p;
                        GroundPredicate(pp, new Dictionary<Parameter, Constant>(),
                            new List<Argument>(pp.Parameters), lGrounded);
                    }
                    else
                        lGrounded.Add((GroundedPredicate)p);
                }
            }
            return lGrounded;
        }

        public List<PlanningAction> GroundAllActions(List<PlanningAction> lActions, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            List<PlanningAction> lGrounded = new List<PlanningAction>();
            Dictionary<string, Constant> dBindings = new Dictionary<string, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }

            }
            foreach (PlanningAction a in lActions)
            {
                if (a is ParametrizedAction)
                {
                    ParametrizedAction pa = (ParametrizedAction)a;
                    lToBind = new List<Parameter>(pa.Parameters);
                    dBindings.Clear();
                    //GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                    GroundAction(pa, lConstants, lToBind, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                }
                else
                {
                    if (a.Preconditions == null || !bCheckConsistency || a.Preconditions.IsTrue(lPredicates, bContainsNegations))
                        lGrounded.Add(a);
                }
            }
            return lGrounded;
        }






        public List<PlanningAction> GroundAllActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            return GroundAllActions(Actions, lPredicates, bContainsNegations, true);
        }

        public List<PlanningAction> GroundAllActions()
        {
            throw new NotImplementedException();
            Problem p = null;
            return GroundAllActions(p, false);
        }


        public List<PlanningAction> GroundAllActions(Problem problem, bool bRemoveConstantPredicates)
        {
            List<PlanningAction> lAllGrounded = new List<PlanningAction>();
            Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
            List<Parameter> lToBind = null;
            List<Constant> lConstants = new List<Constant>();
            HashSet<Predicate> lInitiallyKnownPredicates = new HashSet<Predicate>();
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();

            foreach (GroundedPredicate p in problem.Known)
            {
                lPredicates.Add(p);
                lInitiallyKnownPredicates.Add(p);
            }
            foreach (CompoundFormula cf in problem.Hidden)
            {
                cf.GetAllPredicates(lPredicates);
            }
            Dictionary<string, HashSet<GroundedPredicate>> dPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
            foreach (GroundedPredicate gp in lPredicates)
            {
                if (!gp.Negation)
                {
                    if (!dPredicates.ContainsKey(gp.Name))
                        dPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dPredicates[gp.Name].Add(gp);
                }
            }

            //BUGBUG; //why don't we get the refutet stain grounded?

            bool bNewPredciatesAdded = true;
            int cIterations = 0;
            while (bNewPredciatesAdded)
            {
                List<PlanningAction> lGrounded = new List<PlanningAction>();
                Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates = new Dictionary<string, HashSet<GroundedPredicate>>();
                foreach (PlanningAction a in Actions)
                {
                    if (a is ParametrizedAction)
                    {
                        ParametrizedAction pa = (ParametrizedAction)a;
                        //if (pa.Name.Contains("ls-f") )
                        //   Console.Write("*");
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();

                        bool bNoValidGrounding = false;
                        HashSet<ParametrizedPredicate> lPredicatesToBind = new HashSet<ParametrizedPredicate>();
                        HashSet<Predicate> lOptionalPreconditions = new HashSet<Predicate>();
                        if (pa.Preconditions != null)
                        {
                            foreach (Predicate p in pa.Preconditions.GetAllPredicates())
                            {
                                if (p is ParametrizedPredicate)
                                {
                                    if (!dPredicates.ContainsKey(p.Name) && !p.Negation)
                                        bNoValidGrounding = true;
                                    lPredicatesToBind.Add((ParametrizedPredicate)p);
                                }
                            }
                            lOptionalPreconditions = pa.Preconditions.GetAllOptionalPredicates();
                        }
                        if (pa.Effects != null)
                        {
                            List<CompoundFormula> lConditions = pa.GetConditions();
                            foreach (CompoundFormula cfCondition in lConditions)
                            {
                                foreach (Predicate p in cfCondition.Operands[0].GetAllPredicates())
                                {
                                    if (p is ParametrizedPredicate)
                                    {
                                        if (!dPredicates.ContainsKey(p.Name) && !p.Negation)
                                            bNoValidGrounding = true;
                                        lPredicatesToBind.Add((ParametrizedPredicate)p);
                                        lOptionalPreconditions.Add(p);//all conditions are optional
                                    }
                                }
                            }
                        }

                        //remove negations from the list of predicates to bind
                        HashSet<ParametrizedPredicate> lPredicatesToBindNoNegations = new HashSet<ParametrizedPredicate>();
                        foreach (ParametrizedPredicate p in lPredicatesToBind)
                            if (!p.Negation)
                                lPredicatesToBindNoNegations.Add(p);
                        lPredicatesToBind = lPredicatesToBindNoNegations;


                        if (!bNoValidGrounding)
                        {
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>();
                            GroundAction(pa, dPredicates, lOptionalPreconditions, lToBind, dBindings, lPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates, lPredicates);
                        }
                    }
                    else
                    {
                        ProcessEffects(a, dNewPredicates, lPredicates);
                        lGrounded.Add(a);
                    }
                }

                bNewPredciatesAdded = false;
                foreach (string sKey in dNewPredicates.Keys)
                {
                    if (!dPredicates.ContainsKey(sKey))
                        dPredicates[sKey] = new HashSet<GroundedPredicate>();
                    foreach (GroundedPredicate gp in dNewPredicates[sKey])
                    {
                        if (!dPredicates[sKey].Contains(gp))
                        {
                            dPredicates[sKey].Add(gp);
                            lPredicates.Add(gp);
                            bNewPredciatesAdded = true;
                        }
                    }
                }

                foreach (PlanningAction a in lGrounded)
                {
                    if (!lAllGrounded.Contains(a))
                        lAllGrounded.Add(a);
                }
                cIterations++;

            }

            if (bRemoveConstantPredicates)
            {
                foreach (PlanningAction a in lAllGrounded)
                {
                    if (a.Preconditions is CompoundFormula)
                    {
                        CompoundFormula cfPreconditions = (CompoundFormula)a.Preconditions;
                        CompoundFormula cfClean = new CompoundFormula(cfPreconditions.Operator);
                        foreach (Formula f in cfPreconditions.Operands)
                        {
                            if (f is CompoundFormula)
                                cfClean.AddOperand(f);
                            else
                            {
                                GroundedPredicate gp = (GroundedPredicate)((PredicateFormula)f).Predicate;
                                if (!AlwaysConstant(gp) || !AlwaysKnown(gp) || !lInitiallyKnownPredicates.Contains(gp))
                                    cfClean.AddOperand(gp);
                            }
                        }
                        a.Preconditions = cfClean;
                    }
                }
            }

            return lAllGrounded;
        }



        public List<PlanningAction> GroundAllActuationActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<PlanningAction> lGrounded = new List<PlanningAction>();
            Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
            HashSet<Predicate> lToBind = null;

            foreach (PlanningAction a in Actions)
            {
                if (a.Observe == null)
                {
                    if (a is ParametrizedAction)
                    {
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new HashSet<Predicate>();
                        if (pa.Preconditions != null)
                            pa.Preconditions.GetAllPredicates(lToBind);
                        dBindings.Clear();
                        GroundAction(pa, Constants, new List<Predicate>(lToBind), dBindings, lGrounded, lPredicates, bContainsNegations, true);

                    }
                    else
                        lGrounded.Add(a);
                }
            }
            /*
            List<Action> lFilteredKnown = new List<Action>();
            foreach (Action a in lGrounded)
            {
                PredicateFormula pf = (PredicateFormula)a.Observe;
                if (!lPredicates.Contains(pf.Predicate) &&
                    !lPredicates.Contains(pf.Predicate.Negate()))
                    lFilteredKnown.Add(a);
            }
            */
            return lGrounded;
        }


        public List<PlanningAction> GroundAllObservationActions(IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<PlanningAction> lGrounded = new List<PlanningAction>();
            Dictionary<Parameter, Constant> dBindings = new Dictionary<Parameter, Constant>();
            HashSet<Predicate> lToBind = null;
            //List<Constant> lConstants = new List<Constant>();
            /* can't use these because the observations do not appear in the preconditions
            foreach (Predicate p in lPredicates)
            {
                if (p is GroundedPredicate)
                {
                    GroundedPredicate gp = (GroundedPredicate)p;
                    foreach (Constant c in gp.Constants)
                        if (!lConstants.Contains(c))
                            lConstants.Add(c);
                }
            }
             * */
            foreach (PlanningAction a in Actions)
            {
                if (a.Observe != null)
                {
                    if (a is ParametrizedAction)
                    {
                        /*
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new List<Parameter>(pa.Parameters);
                        dBindings.Clear();
                        GroundAction(pa, Constants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, true);
                         */
                        ParametrizedAction pa = (ParametrizedAction)a;
                        lToBind = new HashSet<Predicate>();
                        if (pa.Preconditions != null)
                            pa.Preconditions.GetAllPredicates(lToBind);
                        dBindings.Clear();
                        GroundAction(pa, Constants, new List<Predicate>(lToBind), dBindings, lGrounded, lPredicates, bContainsNegations, true);

                    }
                    else
                        lGrounded.Add(a);
                }
            }
            List<PlanningAction> lFilteredKnown = new List<PlanningAction>();
            foreach (PlanningAction a in lGrounded)
            {
                PredicateFormula pf = (PredicateFormula)a.Observe;
                if (!lPredicates.Contains(pf.Predicate) &&
                    !lPredicates.Contains(pf.Predicate.Negate()))
                    lFilteredKnown.Add(a);
            }
            return lFilteredKnown;
        }

        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Parameter> lToBind, Dictionary<Parameter, Constant> dBindings,
            List<PlanningAction> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.First();
                lToBind.Remove(p);
                foreach (Constant c in lConstants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p] = c;

                        if (pa.Preconditions != null)
                            fGroundedPreconditions = pa.Preconditions.PartiallyGround(dBindings);
                        if (pa.Preconditions == null || !bCheckConsistency || !fGroundedPreconditions.IsFalse(lPredicates, bContainsNegations))
                            GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                        //else
                        //    Debug.Assert(false);
                    }
                }
                dBindings.Remove(p);
                lToBind.Add(p);
            }
            else
            {
                if (pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += " " + dBindings[p].Name;
                    PlanningAction aGrounded = new PlanningAction(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if ((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>())) &&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }

        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Parameter> lToBind,
            List<PlanningAction> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            Formula fGroundedPreconditions = null;
            List<Predicate> lPre = new List<Predicate>();
            if (pa.Preconditions != null)
                lPre = new List<Predicate>(pa.Preconditions.GetAllPredicates());
            List<Dictionary<Parameter, Constant>> lBindings = FindValidBindings(lToBind, lPre, lPredicates, bContainsNegations);
            foreach (var dBindings in lBindings)
            {
                if (pa.Preconditions != null)
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                if (pa.Preconditions == null || !bCheckConsistency || fGroundedPreconditions.ContainedIn(lPredicates, bContainsNegations))
                {
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += Utilities.DELIMITER_CHAR + dBindings[p].Name;
                    PlanningAction aGrounded = new PlanningAction(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    if (pa.Effects != null)
                        aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                    if (pa.Observe != null)
                        aGrounded.Observe = pa.Observe.Ground(dBindings);
                    if ((pa.Preconditions == null || !aGrounded.Preconditions.IsFalse(new List<Predicate>())) &&
                        (aGrounded.Effects == null || !aGrounded.Effects.IsFalse(new List<Predicate>())))
                        lGrounded.Add(aGrounded);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<Parameter, Constant>> lBindings, Dictionary<Parameter, Constant> dBinding, bool bContainsNegations)
        {
            if (lToBind.Count == 0)
            {
                lBindings.Add(dBinding);
                return;
            }

            Parameter pFirst = lToBind[0];
            List<Parameter> lNewToBind = new List<Parameter>(lToBind);
            lNewToBind.RemoveAt(0);
            foreach (Constant c in Constants)
            {
                if (c.Type == pFirst.Type)
                {
                    Dictionary<Parameter, Constant> dNewBinding = new Dictionary<Parameter, Constant>(dBinding);
                    dNewBinding[pFirst] = c;
                    FindValidBindings(lNewToBind, lBindings, dNewBinding, bContainsNegations);
                }
            }
        }



        private void FindValidBindings(List<Parameter> lToBind, List<Dictionary<Parameter, Constant>> lBindings, Dictionary<Parameter, Constant> dBinding,
            List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            if (lToBind.Count == 0 || lPreconditions.Count == 0)
            {
                if (lToBind.Count != 0)
                    FindValidBindings(lToBind, lBindings, dBinding, bContainsNegations);
                else
                    lBindings.Add(dBinding);
                return;
            }



            Predicate p = lPreconditions[0];
            List<Predicate> lReducedPreconditions = new List<Predicate>();
            for (int i = 1; i < lPreconditions.Count; i++)
                lReducedPreconditions.Add(lPreconditions[i]);

            if (p != null && p is ParametrizedPredicate && ((ParametrizedPredicate)p).Parameters.Count() > 0)
            {
                ParametrizedPredicate pCurrent = (ParametrizedPredicate)p;
                if (pCurrent.Negation && !bContainsNegations)
                {
                    FindValidBindings(lToBind, lBindings, dBinding, lReducedPreconditions, lPredicates, bContainsNegations);
                }
                else
                {
                    List<GroundedPredicate> lMatches = new List<GroundedPredicate>();
                    foreach (GroundedPredicate pGrounded in lPredicates)
                    {
                        if (pCurrent.Name == pGrounded.Name && pCurrent.Negation == pGrounded.Negation)
                            lMatches.Add(pGrounded);
                    }

                    foreach (GroundedPredicate gpMatch in lMatches)
                    {
                        if (gpMatch.ToString().Contains("5-3"))
                            Console.Write("*");
                        Dictionary<Parameter, Constant> dNewBinding = pCurrent.Match(gpMatch, dBinding, this);
                        if (dNewBinding != null)
                        {
                            foreach (var v in dBinding)
                                dNewBinding[v.Key] = v.Value;
                            List<Parameter> lNewToBind = new List<Parameter>();
                            foreach (Parameter param in lToBind)
                            {
                                bool bExists = false;
                                foreach (Parameter s in dNewBinding.Keys)
                                    if (param.Equals(s))
                                        bExists = true;
                                if (!bExists)
                                    lNewToBind.Add(param);
                            }
                            FindValidBindings(lNewToBind, lBindings, dNewBinding, lReducedPreconditions, lPredicates, bContainsNegations);
                        }

                    }
                }

            }
            else
            {
                FindValidBindings(lToBind, lBindings, dBinding, lReducedPreconditions, lPredicates, bContainsNegations);

            }


        }


        private List<Dictionary<Parameter, Constant>> FindValidBindings(List<Parameter> lToBind, List<Predicate> lPreconditions, IEnumerable<Predicate> lPredicates, bool bContainsNegations)
        {
            List<Dictionary<Parameter, Constant>> lBindings = new List<Dictionary<Parameter, Constant>>();
            Dictionary<Parameter, Constant> dBinding = new Dictionary<Parameter, Constant>();

            Predicate pAt = null;
            for (int i = 0; i < lPreconditions.Count; i++)
            {
                if (lPreconditions[i].Name == "at")
                {
                    pAt = lPreconditions[i];
                    lPreconditions[i] = lPreconditions[0];
                    lPreconditions[0] = pAt;
                    break;
                }
            }

            FindValidBindings(lToBind, lBindings, dBinding, lPreconditions, lPredicates, bContainsNegations);
            return lBindings;
        }



        private void GroundAction(ParametrizedAction pa, List<Constant> lConstants,
            List<Predicate> lToBind, Dictionary<Parameter, Constant> dBindings,
            List<PlanningAction> lGrounded, IEnumerable<Predicate> lPredicates, bool bContainsNegations, bool bCheckConsistency)
        {
            if (lToBind.Count > 0)
            {
                Predicate pFirst = lToBind.First();
                lToBind.Remove(pFirst);
                if (pFirst is ParametrizedPredicate)
                {
                    ParametrizedPredicate p = (ParametrizedPredicate)pFirst;
                    foreach (GroundedPredicate pExists in lPredicates)
                    {
                        Dictionary<Parameter, Constant> dNewBindings = p.Match(pExists, dBindings, this);
                        if (dNewBindings != null)
                        {
                            foreach (KeyValuePair<Parameter, Constant> pair in dNewBindings)
                            {
                                dBindings[pair.Key] = pair.Value;
                            }
                            GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                            foreach (KeyValuePair<Parameter, Constant> pair in dNewBindings)
                            {
                                dBindings.Remove(pair.Key);
                            }
                        }
                    }
                }
                else
                {
                    GroundAction(pa, lConstants, lToBind, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
                }
                lToBind.Add(pFirst);
            }
            else
            {
                List<Parameter> lUnboundedParameters = new List<Parameter>();
                foreach (Parameter p in pa.Parameters)
                {
                    if (!dBindings.ContainsKey(p))
                        lUnboundedParameters.Add(p);
                }
                GroundAction(pa, lConstants, lUnboundedParameters, dBindings, lGrounded, lPredicates, bContainsNegations, bCheckConsistency);
            }

        }

        private void GroundAction(ParametrizedAction pa, Dictionary<string, HashSet<GroundedPredicate>> dPredicates, HashSet<Predicate> lOptionalPreconditions,
            List<Parameter> lToBind, Dictionary<Parameter, Constant> dBindings, HashSet<ParametrizedPredicate> lPredicatesToBind, Dictionary<ParametrizedPredicate, GroundedPredicate> dPredicateBindings,
            List<PlanningAction> lGrounded, Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates, HashSet<Predicate> lGroundedPredicates)
        {
            if (lPredicatesToBind.Count > 0)
            {
                ParametrizedPredicate ppCurrent = lPredicatesToBind.First();

                GroundedPredicate gpGrounded = ppCurrent.Ground(dBindings);

                if (gpGrounded == null)
                {
                    if (!dPredicates.ContainsKey(ppCurrent.Name))
                        return;
                    HashSet<GroundedPredicate> lCandidates = dPredicates[ppCurrent.Name];
                    foreach (GroundedPredicate gpCandidate in lCandidates)
                    {

                        Dictionary<Parameter, Constant> dNewBindings = gpCandidate.Bind(ppCurrent);
                        if (ConsistentBindings(dBindings, dNewBindings))
                        {
                            foreach (KeyValuePair<Parameter, Constant> p in dBindings)
                                dNewBindings[p.Key] = p.Value;
                            HashSet<ParametrizedPredicate> lNewPredicatesToBind = new HashSet<ParametrizedPredicate>(lPredicatesToBind);
                            lNewPredicatesToBind.Remove(ppCurrent);
                            Dictionary<ParametrizedPredicate, GroundedPredicate> dNewPredicateBindings = new Dictionary<ParametrizedPredicate, GroundedPredicate>(dPredicateBindings);
                            dNewPredicateBindings[ppCurrent] = gpCandidate;

                            GroundAction(pa, dPredicates, lOptionalPreconditions, lToBind, dNewBindings, lNewPredicatesToBind, dNewPredicateBindings, lGrounded, dNewPredicates, lGroundedPredicates);
                        }
                    }
                }
                else
                {
                    //BUGBUG here - not doing correctly disjunctions - checking conjunction instead...
                    if (gpGrounded.Negation || dPredicates[ppCurrent.Name].Contains(gpGrounded) || lOptionalPreconditions.Contains(ppCurrent))
                    {
                        HashSet<ParametrizedPredicate> lNewPredicatesToBind = new HashSet<ParametrizedPredicate>(lPredicatesToBind);
                        lNewPredicatesToBind.Remove(ppCurrent);
                        GroundAction(pa, dPredicates, lOptionalPreconditions, lToBind, dBindings, lNewPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates, lGroundedPredicates);
                    }
                }
            }
            else
            {
                if (lToBind.Count > dBindings.Keys.Count)
                {
                    foreach(Parameter p in lToBind)
                    {
                        if(!dBindings.ContainsKey(p))
                        {
                            foreach(Constant c in Constants)
                            {
                                if(c.Type == p.Type)
                                {
                                    Dictionary<Parameter, Constant> dNewBindings = new Dictionary<Parameter, Constant>(dBindings);
                                    dNewBindings[p] = c;
                                    GroundAction(pa, dPredicates, lOptionalPreconditions, lToBind, dNewBindings, lPredicatesToBind, dPredicateBindings, lGrounded, dNewPredicates, lGroundedPredicates);
                                }
                            }
                        }
                    }
                }
                else
                {
                    Formula fGroundedPreconditions = null;
                    if (pa.Preconditions != null)
                    {
                        fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                    }
                    string sName = pa.Name;
                    foreach (Parameter p in pa.Parameters)
                        sName += Utilities.DELIMITER_CHAR + dBindings[p].Name;
                    PlanningAction aGrounded = new PlanningAction(sName);
                    aGrounded.Preconditions = fGroundedPreconditions;
                    bool bValidEffects = true;
                    if (pa.Effects != null)
                    {
                        aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                        bValidEffects = ProcessEffects(aGrounded, dNewPredicates, lGroundedPredicates);

                    }
                    if (bValidEffects)
                    {

                        if (pa.Observe != null)
                            aGrounded.Observe = pa.Observe.Ground(dBindings);
                        lGrounded.Add(aGrounded);
                    }
                }
            }
        }

        private bool ProcessEffects(PlanningAction a, Dictionary<string, HashSet<GroundedPredicate>> dNewPredicates, HashSet<Predicate> lGroundedPredicates)
        {
            if (a.Effects == null)
                return true;
            HashSet<Predicate> lApplicableEffects = a.GetApplicableEffects(lGroundedPredicates, false).GetAllPredicates();
            foreach (GroundedPredicate gp in lApplicableEffects)
            {
                if (gp == Utilities.FALSE_PREDICATE)
                    return false;
                if (!gp.Negation)
                {
                    if (!dNewPredicates.ContainsKey(gp.Name))
                        dNewPredicates[gp.Name] = new HashSet<GroundedPredicate>();
                    dNewPredicates[gp.Name].Add(gp);
                }
            }
            return true;
        }

        private bool ConsistentBindings(Dictionary<Parameter, Constant> d1, Dictionary<Parameter, Constant> d2)
        {
            if (d2 == null)
                return false;
            foreach (Parameter p in d1.Keys)
            {
                if (d2.ContainsKey(p))
                {
                    if (!d1[p].Equals(d2[p]))
                        return false;
                }
            }
            return true;
        }


        private void GroundAction(ParametrizedAction pa,
            List<Parameter> lToBind, Dictionary<Parameter, Constant> dBindings,
            List<PlanningAction> lGrounded, Problem problem)
        {
            if (lToBind.Count > 0)
            {
                Parameter p = lToBind.Last();
                lToBind.Remove(p);
                foreach (Constant c in Constants)
                {
                    if (c.Type == p.Type)
                    {
                        dBindings[p] = c;
                        GroundAction(pa, lToBind, dBindings, lGrounded, problem);
                    }
                }
                dBindings.Remove(p);
                lToBind.Add(p);
            }
            else
            {
                Formula fGroundedPreconditions = null;
                if (pa.Preconditions != null)
                {
                    fGroundedPreconditions = pa.Preconditions.Ground(dBindings);
                    if (problem != null && !CheckValidConstantPreconditions(fGroundedPreconditions, problem))
                    {
                        return;
                    }
                }
                string sName = pa.Name;
                foreach (Parameter p in pa.Parameters)
                    sName += " " + dBindings[p].Name;
                PlanningAction aGrounded = new PlanningAction(sName);
                aGrounded.Preconditions = fGroundedPreconditions;
                if (pa.Effects != null)
                    aGrounded.SetEffects(pa.Effects.Ground(dBindings));
                if (pa.Observe != null)
                    aGrounded.Observe = pa.Observe.Ground(dBindings);
                lGrounded.Add(aGrounded);

            }
        }

        private bool CheckValidConstantPreconditions(Formula fGroundedPreconditions, Problem problem)
        {
            if (fGroundedPreconditions is CompoundFormula)
            {
                foreach (Formula fSub in ((CompoundFormula)fGroundedPreconditions).Operands)
                {
                    if (!CheckValidConstantPreconditions(fSub, problem))
                        return false;
                }
                return true;
            }
            else
            {
                PredicateFormula pf = (PredicateFormula)fGroundedPreconditions;
                if (m_lAlwaysConstant.Contains(pf.Predicate.Name) && m_lAlwaysKnown.Contains(pf.Predicate.Name))
                {
                    if (!pf.IsTrue(problem.Known))
                        return false;
                }
                return true;
            }
        }



        private Dictionary<string, string> m_dConstantNameToType;
        public Dictionary<string, string> ConstantNameToType
        {
            get
            {
                if (m_dConstantNameToType == null)
                {
                    m_dConstantNameToType = new Dictionary<string, string>();
                    foreach (Constant c in Constants)
                    {
                        m_dConstantNameToType[c.Name] = c.Type;
                    }
                }
                return m_dConstantNameToType;
            }
        }

        public bool AlwaysKnown(Predicate p)
        {
            return m_lAlwaysKnown.Contains(p.Name);
        }

        public bool Observable(Predicate p)
        {
            return m_lObservable.Contains(p.Name);
        }

        public bool AlwaysConstant(Predicate p)
        {
            return m_lAlwaysConstant.Contains(p.Name);
        }

        public void AddHidden(CompoundFormula cf)
        {
            HashSet<Predicate> lUnknown = new HashSet<Predicate>();
            cf.GetAllPredicates(lUnknown);
            foreach (Predicate p in lUnknown)
                m_lAlwaysKnown.Remove(p.Name);
        }

        public void ComputeAlwaysKnown()
        {
            bool bChanged = true;
            while (bChanged)
            {
                bChanged = false;
                foreach (PlanningAction a in Actions)
                {
                    if (a.HasConditionalEffects)
                    {
                        foreach (CompoundFormula cfCondition in a.GetConditions())
                        {
                            HashSet<Predicate> lIfPredicates = new HashSet<Predicate>();
                            cfCondition.Operands[0].GetAllPredicates(lIfPredicates);
                            bool bAllKnown = true;
                            foreach (Predicate p in lIfPredicates)
                            {
                                if (!m_lAlwaysKnown.Contains(p.Name))
                                    bAllKnown = false;
                            }
                            if (!bAllKnown)
                            {
                                HashSet<Predicate> lThenPredicates = new HashSet<Predicate>();
                                cfCondition.Operands[1].GetAllPredicates(lThenPredicates);
                                foreach (Predicate p in lThenPredicates)
                                {
                                    if (m_lAlwaysKnown.Contains(p.Name))
                                    {
                                        bChanged = true;
                                        m_lAlwaysKnown.Remove(p.Name);
                                    }
                                }
                            }
                        }
                    }
                    if (a.Observe != null)
                    {
                        HashSet<Predicate> lPredicates = a.Observe.GetAllPredicates();
                        foreach (Predicate p in lPredicates)
                        {
                            if (m_lAlwaysKnown.Contains(p.Name))
                            {
                                m_lAlwaysKnown.Remove(p.Name);
                            }
                        }
                    }
                }
            }
        }


        private void WritePredicates(StreamWriter sw, bool bAddInit, int cInit)
        {
            sw.WriteLine("(:predicates");
            foreach (ParametrizedPredicate pp in Predicates)
            {
                sw.Write("(" + pp.Name);//write regular predicate
                foreach (Parameter p in pp.Parameters)
                    sw.Write(" " + p.FullString());
                sw.WriteLine(")");
            }
            if (bAddInit)
            {
                sw.WriteLine("(init)");
                sw.WriteLine("(not-init)");
                for (int i = 0; i < cInit; i++)
                    sw.WriteLine("(init" + i + ")");
            }
            sw.WriteLine(")");
        }
        private void WriteKReplannerActions(StreamWriter sw)
        {
            foreach (PlanningAction a in Actions)
            {
                if (a.Observe == null)
                    WriteAction(sw, a, null);
                else
                    WriteSensor(sw, a);
            }
        }

        public void WriteKReplannerDomain(string sFileName)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (domain " + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw, false, 0);
            sw.WriteLine();
            WriteKReplannerActions(sw);
            sw.WriteLine(")");
            sw.Close();
        }

        public void AddFunction(string sFunctionName)
        {
            Functions.Add(sFunctionName);
        }

        public bool IsFunctionExpression(string s)
        {
            s = s.ToLower();
            return s == "increase" || s == "decrease" || s == "=";
        }

        public CompoundFormula GetOptionsStatement()
        {
            CompoundFormula cfOneof = new CompoundFormula("oneof");
            int cOptions = Math.Max(Options.MAX_OPTIONS, MaxNonDeterministicEffects());
            for (int iOption = 0; iOption < cOptions; iOption++)
            {
                GroundedPredicate gpCurrentOption = new GroundedPredicate(Utilities.OPTION_PREDICATE);
                gpCurrentOption.AddConstant(new Constant(Utilities.OPTION, "opt" + iOption));
                cfOneof.AddOperand(gpCurrentOption);
            }
            return cfOneof;

        }

        public bool IsObservationAction(string sActionName)
        {
            PlanningAction a = GetActionByName(sActionName);
            return a.Observe != null;
        }

        public MemoryStream WriteSimpleDomain(bool bWriteObserveActions = false, bool bAddKToDomainName = true)
        {
            MemoryStream msDomain = new MemoryStream();
            StreamWriter sw = new StreamWriter(msDomain);
            if (bAddKToDomainName)
                sw.WriteLine("(define (domain K" + Name + ")");
            else
                sw.WriteLine("(define (domain " + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            WritePredicates(sw, false, 0);
            sw.WriteLine();
            WriteActions(sw, bWriteObserveActions, false, null);
            sw.WriteLine(")");
            sw.Flush();

            
            return msDomain;

        }

        public MemoryStream WriteDeadendDetectionDomain(string sFileName, Problem p, bool bSimpleChoose = false)
        {
            MemoryStream msDomain = new MemoryStream();
            StreamWriter sw = new StreamWriter(msDomain);
            sw.WriteLine("(define (domain DED" + Name + ")");
            sw.WriteLine("(:requirements :strips :typing)");
            WriteTypes(sw, false);
            WriteConstants(sw);
            sw.WriteLine();
            if (bSimpleChoose)
                WritePredicates(sw, true, p.Unknown.Count());
            else
                WritePredicates(sw, true, p.Hidden.Count());
            sw.WriteLine();
            WriteActions(sw, false, true, null);

            if (bSimpleChoose)
            {
                List<GroundedPredicate> lUnknown = new List<GroundedPredicate>();
                foreach (GroundedPredicate gp in p.Unknown)
                    lUnknown.Add(gp);
                WriteSimpleChooseActions(sw, lUnknown);
            }
            else
            {
                for (int i = 0; i < p.Hidden.Count(); i++)
                {
                    WriteChooseActions(sw, p.Hidden.ElementAt(i), i, p.Hidden.Count());
                }
            }

            sw.WriteLine(")");
            sw.Flush();

            bool bDone = false;
            while (!bDone)
            {
                try
                {
                    msDomain.Position = 0;
                    StreamReader sr = new StreamReader(msDomain);
                    StreamWriter swFile = new StreamWriter(sFileName);
                    swFile.Write(sr.ReadToEnd());
                    swFile.Close();
                    bDone = true;
                }
                catch (Exception e) { }
            }

            return msDomain;

        }



        private void WriteSimpleChooseAction(StreamWriter sw, GroundedPredicate p, int idx, int cInits, bool bValue)
        {
            string spName = p.Name;
            foreach (Constant c in p.Constants)
                spName += Utilities.DELIMITER_CHAR + c.Name;
            spName += Utilities.DELIMITER_CHAR + idx;
            if (bValue)
                spName += "_T";
            else
                spName += "_F";

            sw.WriteLine("(:action Choose_" + spName);

            sw.WriteLine(":precondition (init" + idx + ")");
            CompoundFormula cfAnd = new CompoundFormula("and");
            if (bValue)
                cfAnd.AddOperand(p);
            else
                cfAnd.AddOperand(p.Negate());

            if (idx + 1 < cInits)
                cfAnd.AddOperand(new GroundedPredicate("init" + (idx + 1)));
            cfAnd.AddOperand(new GroundedPredicate("init" + idx).Negate());

            if (idx + 1 == cInits)
            {
                cfAnd.AddOperand(new GroundedPredicate("init").Negate());
                cfAnd.AddOperand(new GroundedPredicate("not-init"));
            }

            sw.WriteLine(":effect " + cfAnd);

            sw.WriteLine(")");
            sw.WriteLine();
        }

        private void WriteSimpleChooseActions(StreamWriter sw, List<GroundedPredicate> lUnknown)
        {
            for (int idx = 0; idx < lUnknown.Count; idx++)
            {
                GroundedPredicate p = lUnknown[idx];
                WriteSimpleChooseAction(sw, p, idx, lUnknown.Count, true);
                WriteSimpleChooseAction(sw, p, idx, lUnknown.Count, false);
            }
        }



        private void WriteChooseActions(StreamWriter sw, CompoundFormula cfInit, int idx, int cInits)
        {
            int iInternalIdx = 0;
            foreach (PredicateFormula pf in cfInit.Operands)
            {
                GroundedPredicate p = (GroundedPredicate)pf.Predicate;
                string spName = p.Name;
                foreach (Constant c in p.Constants)
                    spName += Utilities.DELIMITER_CHAR + c.Name;
                sw.WriteLine("(:action Choose_" + spName + "_" + idx + "_" + iInternalIdx);
                iInternalIdx++;

                sw.WriteLine(":precondition (init" + idx + ")");
                CompoundFormula cfAnd = new CompoundFormula("and");
                if (cfInit.Operator == "oneof" || cfInit.Operator == "or")
                {
                    cfAnd.AddOperand(pf);
                    foreach (PredicateFormula pfOther in cfInit.Operands)
                    {
                        if (pfOther != pf)
                        {
                            cfAnd.AddOperand(pfOther.Negate());
                        }
                    }
                }
                else if (cfInit.Operator == "unknown")
                {
                    cfAnd.AddOperand(pf);
                }
                else
                    throw new NotImplementedException();
                if (idx + 1 < cInits)
                    cfAnd.AddOperand(new GroundedPredicate("init" + (idx + 1)));
                cfAnd.AddOperand(new GroundedPredicate("init" + idx).Negate());

                if (idx + 1 == cInits)
                {
                    cfAnd.AddOperand(new GroundedPredicate("init").Negate());
                    cfAnd.AddOperand(new GroundedPredicate("not-init"));
                }

                sw.WriteLine(":effect " + cfAnd);

                sw.WriteLine(")");
                sw.WriteLine();
            }
        }

        private void WriteActions(StreamWriter sw, bool bWriteObservationActions, bool bInitPrecondition, List<Formula> lDeadends)
        {
            foreach (PlanningAction a in Actions)
            {
                if (bWriteObservationActions || a.Observe == null)
                {
                    List<PlanningAction> lNonConditional = RemoveConditionalEffects(a);
                    foreach (PlanningAction aNonConditional in lNonConditional)
                    {
                        List<PlanningAction> lDeterministic = aNonConditional.RemoveNonDeterministicEffects();
                        foreach (PlanningAction aDet in lDeterministic)
                            WriteAction(sw, aDet, bInitPrecondition, lDeadends);
                    }
                }
            }
            if (bInitPrecondition)
            {
                /*
                sw.WriteLine("(:action EndInit");
                GroundedPredicate gpInit = new GroundedPredicate("init");
                CompoundFormula cfPre = new CompoundFormula("and");
                cfPre.AddOperand(gpInit);
                sw.WriteLine(":precondition " + cfPre);
                CompoundFormula cfEff = new CompoundFormula("and");
                cfEff.AddOperand(gpInit.Negate());

                sw.WriteLine(":effect " + cfEff);

                sw.WriteLine(")");
                sw.WriteLine();
                */
            }
        }

        public bool CompareTo(Domain d)
        {
            foreach (PlanningAction a in Actions)
            {
                bool bFound = false;
                foreach (PlanningAction aOther in d.Actions)
                {
                    if (a.Name == aOther.Name)
                    {
                        bFound = true;
                        if (!a.CompareTo(aOther))
                            return false;
                        break;
                    }
                }
                if (!bFound)
                    return false;
            }
            return true;
        }

        static bool CompareDomains(string sDomain1, string sDomain2)
        {
            Parser p = new Parser();
            Domain d1 = p.ParseDomain(sDomain1);
            Domain d2 = p.ParseDomain(sDomain2);
            return d1.CompareTo(d2);
        }

        public void RemoveUniversalQuantifiers(List<Predicate> lConstantPredicates)
        {
            List<PlanningAction> lFiltered = new List<PlanningAction>();
            foreach (PlanningAction a in Actions)
            {
                PlanningAction aFiltered = a.RemoveUniversalQuantifiers(Constants, lConstantPredicates, this);
                if (aFiltered != null)
                    lFiltered.Add(aFiltered);
                //a.SimplifyConditions();
            }
            Actions = lFiltered;
        }

        public Dictionary<Predicate, HashSet<Predicate>> IdentifyInvariants(List<PlanningAction> lActions)
        {
            Dictionary<Predicate, HashSet<Predicate>> dCandidateMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            Dictionary<Predicate, HashSet<Predicate>> dNotMutex = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (PlanningAction a in lActions)
            {
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                HashSet<Predicate> lEffects = a.GetMandatoryEffects();
                foreach (Predicate p in lEffects)
                {
                    if (p.Negation == false)
                    {
                        foreach (Predicate pTag in lEffects)
                        {
                            if (!pTag.Equals(p) && pTag.Negation == false)
                            {
                                if (!dNotMutex.ContainsKey(p))
                                    dNotMutex[p] = new HashSet<Predicate>();
                                dNotMutex[p].Add(pTag);
                                if (!dNotMutex.ContainsKey(pTag))
                                    dNotMutex[pTag] = new HashSet<Predicate>();
                                dNotMutex[p].Add(p);
                            }
                        }
                    }
                }
                foreach (Predicate p in lPreconditions)
                {
                    Predicate pNegate = p.Negate();
                    if (lEffects.Contains(pNegate))
                    {
                        HashSet<Predicate> lCandidates = new HashSet<Predicate>();
                        foreach (Predicate pTag in lEffects)
                        {
                            //if (pTag.Name == p.Name && pTag.Negation == p.Negation && !pTag.Equals(p))
                            if (p.Similarity(pTag) > 0)
                            {
                                lCandidates.Add(pTag);
                                //if (p.ToString() == "(in-stack B2 S0)" || pTag.ToString() == "(clear B0 S0)")
                                //    Debug.Write("*");

                            }
                        }
                        if (!dCandidateMutex.ContainsKey(p))
                            dCandidateMutex[p] = lCandidates;
                        else
                            dCandidateMutex[p].UnionWith(lCandidates);
                    }

                }

            }
            foreach (PlanningAction a in lActions)
            {
                List<Predicate> lEffects = new List<Predicate>(a.GetMandatoryEffects());
                for (int i = 0; i < lEffects.Count; i++)
                {
                    for (int j = i + 1; j < lEffects.Count; j++)
                    {
                        if (dCandidateMutex.ContainsKey(lEffects[i]))
                            dCandidateMutex[lEffects[i]].Remove(lEffects[j]);
                        if (dCandidateMutex.ContainsKey(lEffects[j]))
                            dCandidateMutex[lEffects[j]].Remove(lEffects[i]);
                    }
                }

            }
            foreach (Predicate p in dCandidateMutex.Keys)
            {
                dMutex[p] = new HashSet<Predicate>();
                foreach (Predicate pTag in dCandidateMutex[p])
                {
                    if (dCandidateMutex[pTag].Contains(p))
                        dMutex[p].Add(pTag);
                }

            }
            List<HashSet<Predicate>> lMutexClosure = new List<HashSet<Predicate>>();
            foreach (Predicate p in dMutex.Keys)
            {
                foreach (Predicate pMutex in dMutex[p])
                {
                    HashSet<Predicate> hsMutex = new HashSet<Predicate>();
                    hsMutex.Add(p);
                    hsMutex.Add(pMutex);
                    Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                    foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                    {
                        if (pair.Value.Count > 1)
                        {
                            HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                            IdentifyMutexClosure(p, pair.Key, pMutex, dMutex, dNotMutex, hsClosure);
                            //                            if (p.Name == "in-stack" || pMutex.Name == "in-stack")
                            //                                Debug.Write("*");
                            lMutexClosure.Add(hsClosure);
                        }
                    }
                }
            }
            /*
            foreach (Predicate p in dMutex.Keys)
            {
                HashSet<Predicate> hsMutex = dMutex[p];
                Dictionary<Argument, HashSet<Predicate>> dInvariants = FindInvariantGroups(p, hsMutex);

                foreach (KeyValuePair<Argument, HashSet<Predicate>> pair in dInvariants)
                {
                    HashSet<Predicate> hsClosure = new HashSet<Predicate>(pair.Value);
                    hsClosure.Add(p);
                    foreach (Predicate pTag in pair.Value)
                    {
                        IdentifyMutexClosure(p, pair.Key, pTag, dMutex, hsClosure);
                    }
                    lMutexClosure.Add(hsClosure);
                }
            }
            */
            Dictionary<Predicate, HashSet<Predicate>> dMutexClosure = new Dictionary<Predicate, HashSet<Predicate>>();
            foreach (HashSet<Predicate> hsClosure in lMutexClosure)
            {
                List<Predicate> lClosure = new List<Predicate>(hsClosure);
                for (int i = 0; i < lClosure.Count; i++)
                {
                    if (!dMutexClosure.ContainsKey(lClosure[i]))
                        dMutexClosure[lClosure[i]] = new HashSet<Predicate>();
                    for (int j = i + 1; j < hsClosure.Count; j++)
                    {
                        if (!dMutexClosure.ContainsKey(lClosure[j]))
                            dMutexClosure[lClosure[j]] = new HashSet<Predicate>();
                        dMutexClosure[lClosure[i]].Add(lClosure[j]);
                        dMutexClosure[lClosure[j]].Add(lClosure[i]);
                    }
                }
            }

            return dMutexClosure;
        }


        public class Pair<T>
        {
            public T T1 { get; private set; }
            public T T2 { get; private set; }
            private int m_iHash;
            public Pair(T t1, T t2)
            {
                T1 = t1;
                T2 = t2;
                m_iHash = 0;
            }
            public override bool Equals(object obj)
            {
                if (obj is Pair<T>)
                {
                    Pair<T> p = (Pair<T>)obj;
                    return T1.Equals(p.T1) && T2.Equals(p.T2) || T1.Equals(p.T2) && T2.Equals(p.T1);
                }
                return false;
            }
            public override int GetHashCode()
            {
                if (m_iHash == 0)
                    m_iHash = T1.GetHashCode() + T2.GetHashCode();
                return m_iHash;
            }
        }

        public Dictionary<Predicate, HashSet<Predicate>> IdentifyInvariantsGraphplan(List<PlanningAction> lActions)
        {

            HashSet<Pair<PlanningAction>> hsActionMutex = new HashSet<Pair<PlanningAction>>();
            HashSet<Pair<Predicate>> hsPropositionMutex = new HashSet<Pair<Predicate>>();
            Dictionary<Predicate, HashSet<PlanningAction>> dMapEffectsToActions = new Dictionary<Predicate, HashSet<PlanningAction>>();
            for (int iAction = 0; iAction < lActions.Count; iAction++)
            {
                PlanningAction a = lActions[iAction];
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                HashSet<Predicate> lEffects = a.GetMandatoryEffects();
                for (int iOtherAction = iAction + 1; iOtherAction < lActions.Count; iOtherAction++)
                {
                    PlanningAction aOther = lActions[iOtherAction];
                    HashSet<Predicate> lOtherPreconditions = aOther.Preconditions.GetAllPredicates();
                    HashSet<Predicate> lOtherEffects = aOther.GetMandatoryEffects();
                    bool bMutex = false;
                    foreach (Predicate p in lPreconditions)
                    {
                        Predicate pNegate = p.Negate();
                        if (lOtherPreconditions.Contains(pNegate))
                        {
                            bMutex = true;
                            break;
                        }
                    }
                    if (!bMutex)
                    {
                        foreach (Predicate p in lEffects)
                        {
                            Predicate pNegate = p.Negate();
                            if (lOtherPreconditions.Contains(pNegate) || lOtherEffects.Contains(pNegate))
                            {
                                bMutex = true;
                                break;
                            }
                        }
                    }
                    if (!bMutex)
                    {
                        foreach (Predicate p in lOtherEffects)
                        {
                            Predicate pNegate = p.Negate();
                            if (lPreconditions.Contains(pNegate))
                            {
                                bMutex = true;
                                break;
                            }
                        }
                    }
                    if (bMutex)
                        hsActionMutex.Add(new Pair<PlanningAction>(a, aOther));
                }
            }
            return null;
        }

        private HashSet<Argument> FindInvariants(Predicate p, HashSet<Predicate> hsMutex)
        {
            HashSet<Argument> hsInvariants = new HashSet<Argument>();
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                for (int i = 0; i < gpGrounded.Constants.Count; i++)
                {
                    Constant c = gpGrounded.Constants[i];
                    bool bInAll = true;
                    foreach (GroundedPredicate gp in hsMutex)
                    {
                        if (!gp.Constants[i].Equals(c))
                        {
                            bInAll = false;
                            break;
                        }
                    }
                    if (bInAll)
                        hsInvariants.Add(c);
                }
            }
            return hsInvariants;
        }

        private Dictionary<Argument, HashSet<Predicate>> FindInvariantGroups(Predicate p, HashSet<Predicate> hsMutex)
        {
            Dictionary<Argument, HashSet<Predicate>> dInvariantGroups = new Dictionary<Argument, HashSet<Predicate>>();
            if (p is GroundedPredicate)
            {
                GroundedPredicate gpGrounded = (GroundedPredicate)p;
                for (int i = 0; i < gpGrounded.Constants.Count; i++)
                {
                    HashSet<Predicate> hsInvariants = new HashSet<Predicate>();
                    Constant c = gpGrounded.Constants[i];
                    foreach (GroundedPredicate gp in hsMutex)
                    {
                        if (gp.Name == p.Name)
                        {
                            if (gp.Constants[i].Equals(c))
                            {
                                hsInvariants.Add(gp);
                            }
                        }
                        else
                        {
                            if (gp.Constants.Contains(c))
                            {
                                hsInvariants.Add(gp);
                            }

                        }
                    }
                    if (hsInvariants.Count > 0)
                        dInvariantGroups[c] = hsInvariants;
                }
            }
            return dInvariantGroups;
        }

        private void IdentifyMutexClosure(Predicate pOrg, Argument aInvariant, Predicate pCurrent, Dictionary<Predicate, HashSet<Predicate>> dMutex, Dictionary<Predicate, HashSet<Predicate>> dNotMutex, HashSet<Predicate> hsClosure)
        {
            HashSet<Predicate> hsCandidates = dMutex[pCurrent];
            foreach (Predicate p in hsCandidates)
            {
                if (!hsClosure.Contains(p))
                {
                    if (pOrg.SameInvariant(p, aInvariant))
                    {
                        bool bValid = true;
                        foreach (Predicate pTag in hsClosure)
                            if (dNotMutex.ContainsKey(p) && dNotMutex[p].Contains(pTag))
                                bValid = false;
                        if (bValid)
                        {
                            hsClosure.Add(p);
                            IdentifyMutexClosure(pOrg, aInvariant, p, dMutex, dNotMutex, hsClosure);
                        }
                    }

                }
            }

        }

        public bool ParentOf(string sType1, string sType2)
        {
            if (sType1 == sType2)
                return true;
            if (TypeHierarchy.ContainsKey(sType2))
                return ParentOf(sType1, TypeHierarchy[sType2]);
            return false;
        }
    }
}
