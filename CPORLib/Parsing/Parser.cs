using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using CPORLib.LogicalUtilities;
using CPORLib.PlanningModel;
using System;

namespace CPORLib.Parsing
{
    public class Parser
    {
        public Parser()
        {

        }

        public bool IgnoreFunctions { get; set; }
        public void ParseDomainAndProblem(string sFileName, string DeadEndFile, out Domain d, out Problem p)
        {
            string sPath = sFileName.Substring(0, sFileName.LastIndexOf(@"\") + 1);
            StreamReader sr = new StreamReader(sFileName);

            /*
            Stack<string> s = ToStack(new StreamReader(sDomainFile));
            Stack<string> s2 = ToStackII(new StreamReader(sDomainFile));

            for (int i = 0; i < s.Count; i++)
                if (s.ElementAt(i) != s2.ElementAt(i))
                    Debug.WriteLine(s.ElementAt(i) + " =/= " + s2.ElementAt(i));
*/
            Stack<string> s = ToStack(sr);
            CompoundExpression eDomain = (CompoundExpression)ToExpression(s);
            CompoundExpression eProblem = (CompoundExpression)ToExpression(s);
            sr.Close();
            d = ParseDomain(eDomain, sPath);
            p = ParseProblem(eProblem, DeadEndFile, d);
            p.PrepareForPlanning();
        }


        public void ParseDomainAndProblem(MemoryStream msModels, out Domain d, out Problem p)
        {
            StreamReader sr = new StreamReader(msModels);

            Stack<string> s = ToStack(sr);
            CompoundExpression eDomain = (CompoundExpression)ToExpression(s);
            CompoundExpression eProblem = (CompoundExpression)ToExpression(s);
            sr.Close();
            d = ParseDomain(eDomain, "");
            p = ParseProblem(eProblem, "", d);
            p.PrepareForPlanning();

        }


        public Domain ParseDomain(string sDomainFile)
        {
            string sPath = sDomainFile.Substring(0, sDomainFile.LastIndexOf(@"\") + 1);
            StreamReader sr = new StreamReader(sDomainFile);


            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();

            return ParseDomain(exp, sPath);
        }

        public Domain ParseDomain(MemoryStream msModel)
        {
            StreamReader sr = new StreamReader(msModel);


            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();

            return ParseDomain(exp, "");
        }


        private Domain ParseDomain(CompoundExpression exp, string sPath)
        {
            Domain d = null;
            foreach (Expression e in exp.SubExpressions)
            {
                if (e is CompoundExpression)
                {
                    CompoundExpression eSub = (CompoundExpression)e;
                    if (eSub.Type == "domain")
                        d = new Domain(eSub.SubExpressions.First().ToString());
                    else if (eSub.Type == ":requirements")
                    {
                    }
                    else if (eSub.Type == ":types")
                    {
                        ReadTypes(eSub, d);
                    }
                    else if (eSub.Type == ":constants")
                    {
                        ReadConstants(eSub, d);
                    }
                    else if (eSub.Type == ":functions")
                    {
                        if (!IgnoreFunctions)
                            ReadFunctions(eSub, d);
                    }
                    else if (eSub.Type == ":predicates")
                    {
                        ReadPredicates(eSub, d);
                    }
                    else if (eSub.Type == ":action")
                    {
                        d.AddAction(ReadAction(eSub, d));
                    }
                }
            }

            return d;
        }

        private void ReadTypes(CompoundExpression eTypes, Domain d)
        {
            List<string> lTypesForHierarchy = new List<string>();
            for (int idx = 0; idx < eTypes.SubExpressions.Count; idx++)
            {
                Expression eType = eTypes.SubExpressions[idx];
                string sType = eType.ToString();
                if (sType == "-")
                {
                    idx++;
                    string sParent = eTypes.SubExpressions[idx].ToString();
                    if (!d.Types.Contains(sParent))
                        d.Types.Add(sParent);
                    foreach (string s in lTypesForHierarchy)
                        d.TypeHierarchy[s] = sParent;
                    lTypesForHierarchy = new List<string>();
                }
                else
                {
                    lTypesForHierarchy.Add(sType);
                    d.Types.Add(sType);
                }
            }
        }

        public Problem ParseProblem(string sProblemFile, Domain d)
        {
            return ParseProblem(sProblemFile, "", d);
        }

        public Problem ParseProblem(string sProblemFile, string sDeadEndFile, Domain d)
        {
            Debug.WriteLine(sProblemFile);
            Debug.WriteLine(sDeadEndFile);
            StreamReader sr = new StreamReader(sProblemFile);
            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();

            Problem p = ParseProblem(exp, sDeadEndFile, d);

            p.PrepareForPlanning();

            return p;

        }
        private Problem ParseProblem(CompoundExpression exp, string sDeadEndFile, Domain d)
        {
            Problem p = null;
            CompoundExpression eSub = null;
            foreach (Expression e in exp.SubExpressions)
            {
                //Console.WriteLine("Parsing: " + e);
                eSub = (CompoundExpression)e;
                if (eSub.Type == "problem")
                {
                    p = new Problem(eSub.SubExpressions.First().ToString(), d);
                }
                if (eSub.Type == ":domain")
                {
                    if (eSub.SubExpressions.First().ToString() != d.Name)
                        throw new InvalidDataException("Domain and problem files don't match!");
                }
                if (eSub.Type == ":objects")
                {
                    ReadConstants(eSub, d);
                }
                if (eSub.Type == ":init")
                {
                    CompoundExpression eAnd = (CompoundExpression)eSub.SubExpressions.First();
                    if (eAnd.Type == "and")
                        ReadInitState(p, d, eAnd);
                    else
                        ReadInitState(p, d, eSub);
                    //throw new InvalidDataException("Expecting 'and', got " + eAnd.Type);
                }
                if (eSub.Type == ":goal")
                    ReadGoal(p, d, eSub.SubExpressions[0]);
                if (eSub.Type == ":metric")
                    ReadMetric(p, d, eSub);
            }
            //p.AddReasoningActions(); not needed as long as we use FF to do the planning for us
            
            if (sDeadEndFile != "")
                p.DeadEndList = ParseDeadEndsProblemFormula(sDeadEndFile, d);
            

            


            return p;
        }



        private void ReadFunctions(CompoundExpression eFunctions, Domain d)
        {
            foreach (Expression eSub in eFunctions.SubExpressions)
            {
                if (eSub.ToString() != ":functions")
                {
                    CompoundExpression eFunction = (CompoundExpression)eSub;
                    //BUGBUG - only reading non parametrized functions for now
                    d.AddFunction("(" + eFunction.Type + ")");
                }

            }
        }

        private void ReadConstants(CompoundExpression exp, Domain d)
        {
            string sType = "?", sExp = "";
            List<string> lUndefined = new List<string>();
            for (int iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
            {
                sExp = exp.SubExpressions[iExpression].ToString().Trim();
                if (sExp == "-")
                {
                    sType = exp.SubExpressions[iExpression + 1].ToString();
                    iExpression++;
                    foreach (string sName in lUndefined)
                        d.AddConstant(new Constant(sType, sName));
                    lUndefined.Clear();
                }
                else if (!sExp.StartsWith(":"))
                {
                    lUndefined.Add(sExp);
                }
            }
            if (lUndefined.Count > 0)
            {
                //supporting objects with undefined types as type "OBJ"
                foreach (string sName in lUndefined)
                    d.AddConstant(new Constant("OBJ", sName));
                //throw new NotImplementedException();
            }

        }
        private void ReadPredicates(CompoundExpression exp, Domain d)
        {
            foreach (Expression e in exp.SubExpressions)
            {
                Predicate p = ReadPredicate((CompoundExpression)e, d);
                d.AddPredicate(p);
            }
        }
        private Predicate ReadPredicate(CompoundExpression exp, Domain d)
        {
            ParametrizedPredicate pp = new ParametrizedPredicate(exp.Type);
            int iExpression = 0;
            Parameter p = null;
            string sName = "";
            List<Parameter> lUntypedParameters = new List<Parameter>();
            for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
            {
                sName = exp.SubExpressions[iExpression].ToString();
                if (sName == "-")
                {
                    string sType = exp.SubExpressions[iExpression + 1].ToString();
                    foreach (Parameter pUntyped in lUntypedParameters)
                        pUntyped.Type = sType;
                    lUntypedParameters.Clear();
                    iExpression++;//skip the "-" and the type
                }
                else
                {
                    p = new Parameter("", sName);
                    lUntypedParameters.Add(p);
                    pp.AddParameter(p);
                }
            }
            if (d.Types.Count == 1)
            {
                foreach (Parameter pUntyped in lUntypedParameters)
                    pUntyped.Type = d.Types[0];
            }
            return pp;
        }

        private GroundedPredicate ReadGroundedPredicate(CompoundExpression exp, Domain d)
        {
            GroundedPredicate gp = new GroundedPredicate(exp.Type);
            int iExpression = 0;
            Constant c = null;
            string sName = "";
            for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
            {
                sName = exp.SubExpressions[iExpression].ToString();
                c = d.GetConstant(sName);
                if (c == null)
                    throw new Exception("Unknown constant " + sName);
                gp.AddConstant(c);
            }
            return gp;
        }




        private PlanningAction ReadAction(CompoundExpression exp, Domain d)
        {
            string sName = exp.SubExpressions[0].ToString();
            PlanningAction pa = null;
            int iExpression = 0;
            for (iExpression = 1; iExpression < exp.SubExpressions.Count; iExpression++)
            {
                if (exp.SubExpressions[iExpression].ToString() == ":parameters")
                {
                    CompoundExpression ceParams = (CompoundExpression)exp.SubExpressions[iExpression + 1];
                    if (ceParams.Type != "N/A")
                    {
                        pa = new ParametrizedAction(sName);
                        ReadParameters((CompoundExpression)exp.SubExpressions[iExpression + 1], (ParametrizedAction)pa);
                    }
                    iExpression++;
                }
                else if (exp.SubExpressions[iExpression].ToString() == ":effect")
                {
                    if (pa == null)
                        pa = new PlanningAction(sName);
                    ReadEffect((CompoundExpression)exp.SubExpressions[iExpression + 1], pa, d, pa is ParametrizedAction);
                    iExpression++;
                }
                else if (exp.SubExpressions[iExpression].ToString() == ":precondition")
                {
                    if (pa == null)
                        pa = new PlanningAction(sName);
                    ReadPrecondition((CompoundExpression)exp.SubExpressions[iExpression + 1], pa, d, pa is ParametrizedAction);
                    iExpression++;
                }
                else if (exp.SubExpressions[iExpression].ToString() == ":observe")
                {
                    if (pa == null)
                        pa = new PlanningAction(sName);
                    ReadObserve((CompoundExpression)exp.SubExpressions[iExpression + 1], pa, d, pa is ParametrizedAction);
                    iExpression++;
                }
            }
            return pa;
        }

        private void ReadParameters(CompoundExpression exp, ParametrizedAction pa)
        {
            //unfortunately, expressions have a weird non standard structure with no type - (?i - pos ?j - pos )
            //so we must have a special case 
            List<string> lTokens = exp.ToTokenList();
            List<string> lNames = new List<string>();
            string sType = "";
            int iCurrent = 0;
            while (iCurrent < lTokens.Count)
            {
                if (lTokens[iCurrent] == "-")
                {
                    sType = lTokens[iCurrent + 1];
                    foreach (string sName in lNames)
                        pa.AddParameter(new Parameter(sType, sName));
                    lNames = new List<string>();
                    sType = "";
                    iCurrent += 2;
                }
                else
                {
                    lNames.Add(lTokens[iCurrent]);
                    iCurrent++;
                }
            }
            if (lNames.Count != 0) //allowing no types specified
            {
                foreach (string sName in lNames)
                    pa.AddParameter(new Parameter("OBJ", sName));
            }

        }

        private Formula ReadFormula(CompoundExpression exp, Dictionary<string, string> dParameterNameToType, bool bParamterized, Domain d)
        {
            bool bPredicate = true;
            //Debug.WriteLine(exp);
            if (d != null && d.IsFunctionExpression(exp.Type))
            {
                if (IgnoreFunctions)
                    return null;
                Predicate p = ReadFunctionExpression(exp, dParameterNameToType, d);
                return new PredicateFormula(p);
            }
            else if (IsUniversalQuantifier(exp))
            {
                CompoundExpression eParameter = (CompoundExpression)exp.SubExpressions[0];
                CompoundExpression eBody = (CompoundExpression)exp.SubExpressions[1];
                string sParameter = eParameter.Type;
                string sType = eParameter.SubExpressions[1].ToString();
                dParameterNameToType[sParameter] = sType;
                ParametrizedFormula cfQuantified = new ParametrizedFormula(exp.Type);
                cfQuantified.Parameters[sParameter] = sType;
                Formula fBody = ReadFormula(eBody, dParameterNameToType, true, d);
                cfQuantified.AddOperand(fBody);
                return cfQuantified;
            }
            else if (exp.Type == "probabilistic")
            {
                ProbabilisticFormula pf = new ProbabilisticFormula();
                int iExpression = 0;
                for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression += 2)
                {
                    //if (exp.SubExpressions[iExpression] is StringExpression)
                    //    throw new InvalidDataException();
                    string sProb = exp.SubExpressions[iExpression].ToString();
                    double dProb = 0.0;
                    if (sProb.Contains("/"))
                    {
                        string[] a = sProb.Split('/');
                        dProb = double.Parse(a[0]) / double.Parse(a[1]);
                    }
                    else
                    {
                        dProb = double.Parse(sProb);
                    }
                    Formula f = ReadFormula((CompoundExpression)exp.SubExpressions[iExpression + 1], dParameterNameToType, bParamterized, d);
                    pf.AddOption(f, dProb);
                }
                return pf;
            }
            else
            {
                foreach (Expression eSub in exp.SubExpressions)
                {
                    if (eSub is CompoundExpression)
                    {
                        bPredicate = false;
                        break;
                    }
                }
                if (bPredicate)
                    return ReadPredicate(exp, dParameterNameToType, bParamterized, d);
                else
                {
                    CompoundFormula cf = new CompoundFormula(exp.Type);
                    int iExpression = 0;
                    for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
                    {
                        if (exp.SubExpressions[iExpression] is StringExpression)
                            throw new InvalidDataException();
                        Formula f = ReadFormula((CompoundExpression)exp.SubExpressions[iExpression], dParameterNameToType, bParamterized, d);
                        cf.SimpleAddOperand(f);
                    }
                    if (cf.Operator == "not" && cf.Operands[0] is PredicateFormula)
                    {
                        PredicateFormula fNegate = new PredicateFormula(((PredicateFormula)cf.Operands[0]).Predicate.Negate());
                        return fNegate;
                    }
                    return cf;
                }
            }
        }

        private bool IsUniversalQuantifier(CompoundExpression exp)
        {
            return exp.Type.ToLower() == "forall" || exp.Type.ToLower() == "exists";
        }


        private Formula ReadGroundedFormula(CompoundExpression exp, Domain d)
        {
            bool bPredicate = true;
            if (IsUniversalQuantifier(exp))
            {
                CompoundExpression eParameter = (CompoundExpression)exp.SubExpressions[0];
                CompoundExpression eBody = (CompoundExpression)exp.SubExpressions[1];
                string sParameter = eParameter.Type;
                string sType = eParameter.SubExpressions[1].ToString();
                Dictionary<string, string> dParameterNameToType = new Dictionary<string, string>();
                dParameterNameToType[sParameter] = sType;
                ParametrizedFormula cfQuantified = new ParametrizedFormula(exp.Type);
                cfQuantified.Parameters[sParameter] = sType;
                Formula fBody = ReadFormula(eBody, dParameterNameToType, true, d);
                cfQuantified.AddOperand(fBody);
                return cfQuantified;
            }
            foreach (Expression eSub in exp.SubExpressions)
            {
                if (eSub is CompoundExpression)
                {
                    bPredicate = false;
                    break;
                }
            }
            if (bPredicate)
                return new PredicateFormula(ReadGroundedPredicate(exp, d));
            else
            {
                CompoundFormula cf = new CompoundFormula(exp.Type);
                int iExpression = 0;
                for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
                {
                    Formula f = ReadGroundedFormula((CompoundExpression)exp.SubExpressions[iExpression], d);
                    cf.SimpleAddOperand(f);
                }
                if (cf.Operator == "not" && cf.Operands[0] is PredicateFormula)
                {
                    return new PredicateFormula(((PredicateFormula)cf.Operands[0]).Predicate.Negate());
                }
                return cf;
            }
        }

        private Formula ReadPredicate(CompoundExpression exp, Dictionary<string, string> dParameterNameToType, bool bParametrized, Domain d)
        {
            Predicate p = null;
            int iExpression = 0;
            string sName = "";

            if (bParametrized)
                p = new ParametrizedPredicate(exp.Type);
            else
                p = new GroundedPredicate(exp.Type);
            bool bAllConstants = true;
            for (iExpression = 0; iExpression < exp.SubExpressions.Count; iExpression++)
            {
                sName = exp.SubExpressions[iExpression].ToString();
                if (bParametrized)
                {
                    Argument a = null;
                    if (dParameterNameToType.ContainsKey(sName))
                    {
                        a = new Parameter(dParameterNameToType[sName], sName);
                        bAllConstants = false;
                    }
                    else if (d.ConstantNameToType.ContainsKey(sName))
                    {
                        a = new Constant(d.ConstantNameToType[sName], sName);
                    }
                    else
                        throw new Exception("Unknown parameter/constant " + sName + " in " + exp);
                    
                    ((ParametrizedPredicate)p).AddParameter(a);
                }
                else
                {
                    try
                    {
                        Constant c = new Constant(d.ConstantNameToType[sName], sName);
                        ((GroundedPredicate)p).AddConstant(c);
                    }
                    catch (Exception e)
                    {
                        Debug.WriteLine("");
                    }
                }
            }
            if (bParametrized)
                if (!MatchParametersToPredicateDeclaration((ParametrizedPredicate)p, d))
                    throw new Exception("Paramter does not match predicate declaration " + p);

            if (bParametrized && bAllConstants)
            {
                GroundedPredicate gp = new GroundedPredicate(p.Name);
                foreach (Constant c in ((ParametrizedPredicate)p).Parameters)
                    gp.AddConstant(c);
                p = gp;
            }


            PredicateFormula vf = new PredicateFormula(p);
            return vf;
        }

        private bool MatchParametersToPredicateDeclaration(ParametrizedPredicate pp, Domain d)
        {
            foreach (Predicate pDefinition in d.Predicates)
            {
                if (pDefinition.Name == pp.Name)
                {
                    if (pDefinition is ParametrizedPredicate)
                    {
                        ParametrizedPredicate ppDefinition = (ParametrizedPredicate)pDefinition;
                        if (pp.Parameters.Count() != ppDefinition.Parameters.Count())
                            return false;
                        for (int i = 0; i < pp.Parameters.Count(); i++)
                        {
                            if (ppDefinition.Parameters.ElementAt(i).Type == "")
                                ppDefinition.Parameters.ElementAt(i).Type = pp.Parameters.ElementAt(i).Type;
                            else
                            {
                                if (d.ParentOf(ppDefinition.Parameters.ElementAt(i).Type, pp.Parameters.ElementAt(i).Type))
                                    return true;
                                if (ppDefinition.Parameters.ElementAt(i).Type != pp.Parameters.ElementAt(i).Type)
                                    return false;
                            }
                        }
                        return true;
                    }
                }
            }
            return false;
        }

        private void ReadEffect(CompoundExpression exp, PlanningAction pa, Domain d, bool bParametrized)
        {
            string sOperator = exp.Type;
            Formula f = null;
            if (pa is ParametrizedAction)
                f = ReadFormula(exp, ((ParametrizedAction)pa).ParameterNameToType, bParametrized, d);
            else
                f = ReadFormula(exp, d.ConstantNameToType, bParametrized, d);
            pa.SetEffects(f);

        }
        private void ReadPrecondition(CompoundExpression exp, PlanningAction pa, Domain d, bool bParametrized)
        {
            string sOperator = exp.Type;
            Formula f = null;
            if (pa is ParametrizedAction)
                f = ReadFormula(exp, ((ParametrizedAction)pa).ParameterNameToType, bParametrized, d);
            else
                f = ReadFormula(exp, d.ConstantNameToType, bParametrized, d);
            pa.Preconditions = f;
        }
        private void ReadObserve(CompoundExpression exp, PlanningAction pa, Domain d, bool bParametrized)
        {
            string sOperator = exp.Type;
            Formula f = null;
            if (pa is ParametrizedAction)
                f = ReadFormula(exp, ((ParametrizedAction)pa).ParameterNameToType, bParametrized, d);
            else
                f = ReadFormula(exp, d.ConstantNameToType, bParametrized, d);
            pa.Observe = f;
        }

        public static string ListToString(IList l)
        {
            if (l.Count == 0)
                return "";
            string s = "";
            for (int i = 0; i < l.Count - 1; i++)
            {
                s += l[i].ToString() + " ";
            }
            s += l[l.Count - 1] + "";
            return s;
        }

        public static string ListToString(IList l, int cTabs)
        {
            if (l.Count == 0)
                return "";
            string s = "";
            for (int i = 0; i < l.Count - 1; i++)
            {
                if (l[i] is CompoundFormula)
                    s += ((CompoundFormula)l[i]).ToString(cTabs);
                else
                    s += l[i].ToString() + " ";
            }
            if (l[l.Count - 1] is CompoundFormula)
                s += ((CompoundFormula)l[l.Count - 1]).ToString(cTabs) + "";
            else
                s += l[l.Count - 1] + "";
            return s;
        }

        public static string ListToStringII(IList l)
        {
            if (l.Count == 0)
                return "()";
            string s = "(";
            for (int i = 0; i < l.Count - 1; i++)
            {
                s += l[i].ToString() + " ";
            }
            s += l[l.Count - 1] + ")";
            return s;
        }
        private void ReadMetric(Problem p, Domain d, CompoundExpression eSub)
        {
            if (!IgnoreFunctions)
                p.AddMetric(eSub.ToString());
        }

        private void ReadGoal(Problem p, Domain d, Expression eGoal)
        {
            Formula fGoal = ReadGroundedFormula((CompoundExpression)eGoal, d);
            p.Goal = fGoal;
        }

        private void ReadInitState(Problem p, Domain d, CompoundExpression eInitState)
        {

            foreach (Expression e in eInitState.SubExpressions)
            {
                CompoundExpression eSub = (CompoundExpression)e;
                //Debug.WriteLine(eSub);
                if (d.IsFunctionExpression(eSub.Type))
                {
                    if (!IgnoreFunctions)
                        p.AddKnown(ReadFunctionExpression(eSub, null, d));
                }
                else if (d.ContainsPredicate(eSub.Type))
                {
                    GroundedPredicate gp = ReadGroundedPredicate(eSub, d);
                    p.AddKnown(gp);
                }
                else
                {
                    if (eSub.Type != "unknown")
                    {
                        Formula f = ReadGroundedFormula(eSub, d);
                        if (f is CompoundFormula)
                            p.AddHidden((CompoundFormula)f);
                        if (f is PredicateFormula)//this happens in (not (p)) statments
                            p.AddKnown(((PredicateFormula)f).Predicate);
                    }
                    else
                    {
                        //causing a problem - add operand does some basic reasoning - adding p and ~p results in true for or statements.
                        //skipping unknown for now...

                        Predicate pUnknown = ReadGroundedPredicate((CompoundExpression)eSub.SubExpressions[0], d);
                        CompoundFormula cfOr = new CompoundFormula("or");
                        cfOr.SimpleAddOperand(pUnknown);
                        cfOr.SimpleAddOperand(pUnknown.Negate());
                        p.AddHidden(cfOr);

                    }
                }
            }
            p.ComputeRelevanceClosure();
        }

        private Predicate ReadFunctionExpression(CompoundExpression exp, Dictionary<string, string> dParameterNameToType, Domain d)
        {
            Constant c = null;
            string sName = exp.SubExpressions[0].ToString();

            if (exp.Type == "=")
            {
                string sParam1 = exp.SubExpressions[0].ToString();
                string sParam2 = exp.SubExpressions[1].ToString();
                if (!dParameterNameToType.ContainsKey(sParam1))
                    throw new ArgumentException("First argument of = must be a parameter");
                ParametrizedPredicate pp = new ParametrizedPredicate("=");
                pp.AddParameter(new Parameter(dParameterNameToType[sParam1], sParam1));
                if (dParameterNameToType.ContainsKey(sParam2))
                    pp.AddParameter(new Parameter(dParameterNameToType[sParam2], sParam2));
                else
                    pp.AddParameter(new Constant(d.ConstantNameToType[sParam2], sParam2));
                return pp;

            }


            GroundedPredicate p = new GroundedPredicate(exp.Type);
            double dValue = 0.0;
            if (d.Functions.Contains(sName))
                c = new Constant("Function", sName);
            else
                throw new ArgumentException("First argument of increase or decrease must be a function");
            p.AddConstant(c);

            sName = exp.SubExpressions[1].ToString();
            if (double.TryParse(sName, out dValue))
                c = new Constant("Number", sName);
            else
                throw new ArgumentException("Second argument of increase or decrease must be a number");
            p.AddConstant(c);
            return p;
        }
        public Stack<string> ToStack(StreamReader sr)
        {
            Stack<string> lStack = new Stack<string>();
            char[] aDelimiters = { ' ', '\n', '(', ')' };
            Stack<string> sTokens = new Stack<string>();
            string sToken = "";
            while (!sr.EndOfStream)
            {
                string sLine = sr.ReadLine();
                sLine = sLine.Trim().ToLower();
                if (sLine.StartsWith(";;") && sLine.Contains("cell for initial open"))
                    sLine = sLine.Substring(2);
                //if(sLine.Contains("move0"))
                //    Debug.WriteLine("BUGBUG");
                if (sLine.Contains(";"))
                    sLine = sLine.Substring(0, sLine.IndexOf(";")).Trim();
                sLine += " ";
                foreach (char c in sLine)
                {
                    if (aDelimiters.Contains(c))
                    {
                        sToken = sToken.Trim();
                        sTokens.Push(sToken);
                        sTokens.Push(c + "");
                        sToken = "";
                    }
                    else
                    {
                        sToken += c;
                    }
                }
                sTokens.Push("\n");
            }
            sToken = sToken.Trim();
            if (sToken.Length > 0)
                sTokens.Push(sToken);
            Stack<string> sReveresed = new Stack<string>();
            while (sTokens.Count > 0)
            {
                sToken = sTokens.Pop();
                if (sToken.Contains("\n"))
                    sToken = "\n";
                else
                    sToken = sToken.Trim();

                if (sToken.Length > 0)
                    sReveresed.Push(sToken);
            }
            return sReveresed;
        }

        private string ReadToEnd(StreamReader sr)
        {
            string sAll = "";
            while (!sr.EndOfStream)
            {
                string sLine = sr.ReadLine();
                if (sLine.Contains(";"))
                    sLine = sLine.Substring(0, sLine.IndexOf(";")).Trim();
                if (sLine.Length > 0)
                    sAll += sLine + " ";
            }
            return sAll;
        }

        private Expression ToExpression(StreamReader sr)
        {
            Stack<string> s = ToStack(sr);
            while (s.Count > 0 && s.Peek() == "\n")
                s.Pop();
            Expression e = ToExpression(s);
            return e;
        }

        private Expression ToExpression(Stack<string> sStack)
        {
            string sToken = sStack.Pop();
            while (sToken.Trim() == "" || sToken == "\0")
                sToken = sStack.Pop();
            if (sToken == "(")
            {
                bool bDone = false;
                CompoundExpression exp = new CompoundExpression();
                sToken = sStack.Pop();
                if (sToken == ")")
                {
                    exp.Type = "N/A";
                    bDone = true;
                }
                else
                    exp.Type = sToken;
                while (!bDone)
                {
                    if (sStack.Count == 0)
                        throw new InvalidDataException("Exp " + exp.Type + " was not closed");
                    sToken = sStack.Pop();
                    if (sToken == "\n")
                    {
                        if (exp.SubExpressions.Count > 0)
                            exp.SubExpressions.Last().EndOfLine = true;
                    }
                    else
                    {
                        if (sToken == ")")
                            bDone = true;
                        else
                        {
                            sStack.Push(sToken);
                            exp.SubExpressions.Add(ToExpression(sStack));
                        }
                    }
                }
                return exp;
            }
            else
            {
                return new StringExpression(sToken);
            }
        }

        public List<List<GroundedPredicate>> ParseDeadEndsProblem(string sProblemFile, Domain d)
        {
            List<List<GroundedPredicate>> listDeadEnds = new List<List<GroundedPredicate>>();

            StreamReader sr = new StreamReader(sProblemFile);
            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();
            CompoundExpression eSub = null;
            CompoundExpression eeSub = null;
            Problem p = null;
            foreach (Expression e in exp.SubExpressions)
            {
                eSub = (CompoundExpression)e;
                if (eSub.Type == "problem")
                {
                    p = new Problem(eSub.SubExpressions.First().ToString(), d);
                }
                if (eSub.Type == ":domain")
                {
                    if (eSub.SubExpressions.First().ToString() != d.Name)
                        throw new InvalidDataException("Domain and problem files don't match!");
                }
                if (eSub.Type == ":objects")
                {
                    ReadConstants(eSub, d);
                }
                if (eSub.Type == ":init")
                {
                    foreach (Expression sube in eSub.SubExpressions)
                    {
                        eeSub = (CompoundExpression)sube;
                        //CompoundExpression eAnd = (CompoundExpression)eSub.SubExpressions.First();
                        if (eeSub.Type == "and")
                            listDeadEnds.Add(ReadAnd(eeSub, d));
                        else
                            listDeadEnds.Add(new List<GroundedPredicate> { ReadGroundedPredicate(eeSub, d) });
                        //throw new InvalidDataException("Expecting 'and', got " + eAnd.Type);
                    }
                }
            }
            return listDeadEnds;
        }

        public List<Formula> ParseDeadEndsProblemFormula(string sProblemFile, Domain d)
        {
            List<Formula> listDeadEndsFormula = new List<Formula>();

            StreamReader sr = new StreamReader(sProblemFile);
            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();
            CompoundExpression eSub = null;
            CompoundExpression eeSub = null;
            Problem p = null;
            foreach (Expression e in exp.SubExpressions)
            {
                eSub = (CompoundExpression)e;
                if (eSub.Type == "problem")
                {
                    p = new Problem(eSub.SubExpressions.First().ToString(), d);
                }
                if (eSub.Type == ":domain")
                {
                    if (eSub.SubExpressions.First().ToString() != d.Name)
                        throw new InvalidDataException("Domain and problem files don't match: " + eSub.SubExpressions.First().ToString() + "!=" + d.Name);
                }
                if (eSub.Type == ":objects")
                {
                    ReadConstants(eSub, d);
                }
                if (eSub.Type == ":init")
                {
                    foreach (Expression sube in eSub.SubExpressions)
                    {
                        eeSub = (CompoundExpression)sube;
                        //CompoundExpression eAnd = (CompoundExpression)eSub.SubExpressions.First();
                        if (eeSub.Type == "and")
                        {
                            Formula f = ReadGroundedFormula(eeSub, d);
                            listDeadEndsFormula.Add(f);
                        }
                        //listDeadEnds.Add(ReadAnd(eeSub, d));
                        else
                        {
                            GroundedPredicate gp = ReadGroundedPredicate(eeSub, d);
                            Formula f = new PredicateFormula(gp);
                            listDeadEndsFormula.Add(f);

                        }
                        //throw new InvalidDataException("Expecting 'and', got " + eAnd.Type);
                    }
                }
            }
            return listDeadEndsFormula;
        }

        private List<GroundedPredicate> ReadAnd(CompoundExpression eInitState, Domain d)
        {
            List<GroundedPredicate> listDeadEndAnd = new List<GroundedPredicate>();

            foreach (Expression e in eInitState.SubExpressions)
            {

                CompoundExpression eSub = (CompoundExpression)e;
                listDeadEndAnd.Add(ReadGroundedPredicate(eSub, d));

            }
            return listDeadEndAnd;
        }

        public CompoundFormula ParseFormula(string sFile, Domain d)
        {
            string sPath = sFile.Substring(0, sFile.LastIndexOf(@"\") + 1);
            StreamReader sr = new StreamReader(sFile);
            CompoundExpression exp = (CompoundExpression)ToExpression(sr);
            sr.Close();
            Formula cf = ReadFormula(exp, null, false, d);
            return (CompoundFormula)cf;
        }




    }
}
