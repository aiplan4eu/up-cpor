using CPORLib.FFCS;
using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using CPORLib.Tools;

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using static CPORLib.Tools.Options;
using Action = CPORLib.PlanningModel.PlanningAction;

#if PYTHONNET
using Python.Runtime;
#endif

namespace CPORLib.Algorithms
{
    public class PlannerBase
    {
#if PYTHONNET
        public PyObject UPClassicalPlanner { set; get; }
        public PyObject UPParser { set; get; }
#endif

        protected Domain Domain;
        protected Problem Problem;

        private int m_iInfoLevel = 1;
        public int InfoLevel { 
            get
            {
                return m_iInfoLevel;
            }
            set
            {
                m_iInfoLevel = value;
                if(m_iInfoLevel > 1)
                    FFUtilities.Verbose = true;
                else
                    FFUtilities.Verbose = false;
            }
            
        }

        public ExecutionData ExecutionData { get; set; }

        public PlannerBase(Domain d, Problem p)
        {
            Domain = d;
            Problem = p;
            
            ExecutionData = new ExecutionData("", "", d, p, Options.DeadendStrategy);

            Problem.PrepareForPlanning();


        }


        protected bool StuckInLoopStateBased(int cActions, PartiallySpecifiedState pssCurrent, List<List<string>> lExecutedPlans)
        {
            if (cActions >= 100000)
                return true;
            //used only for finding loops
            if (lExecutedPlans.Count > 5)
            {
                if (pssCurrent.Equals(pssCurrent.Predecessor.Predecessor))
                {
                    if (pssCurrent.Predecessor.Equals(pssCurrent.Predecessor.Predecessor.Predecessor))
                    {
                        if (Utilities.SameList(lExecutedPlans[lExecutedPlans.Count - 1], lExecutedPlans[lExecutedPlans.Count - 3]))
                        {
                            if (Utilities.SameList(lExecutedPlans[lExecutedPlans.Count - 2], lExecutedPlans[lExecutedPlans.Count - 4]))
                            {
                                //throw new Exception("stuck in a loop");
                                //Debug.WriteLine("Stuck in a loop");
                            }
                        }
                    }
                }
                bool bAllEmpty = true;
                for (int i = 1; i <= 4; i++)
                    if (lExecutedPlans[lExecutedPlans.Count - i].Count != 0)
                        bAllEmpty = false;
                if (bAllEmpty)
                    return true;
            }
            return false;
        }

        protected bool ComparePlans(List<string> l1, List<string> l2)
        {
            if (l1.Count != l2.Count)
                return false;
            for (int i = 0; i < l1.Count; i++)
                if (l1[i] != l2[i])
                    return false;
            return true;
        }

        protected bool StuckInLoopPlanBased(int cActions, PartiallySpecifiedState pssCurrent, List<List<string>> lExecutedPlans)
        {
            if (cActions >= 100000)
                return true;
            //used only for finding loops
            int cPlans = lExecutedPlans.Count;
            if (cPlans > 5)
            {
                if (ComparePlans(lExecutedPlans[cPlans - 1], lExecutedPlans[cPlans - 3]))
                {
                    if (ComparePlans(lExecutedPlans[cPlans - 2], lExecutedPlans[cPlans - 4]))
                    {
                        return true;
                    }
                }
                bool bAllEmpty = true;
                for (int i = 1; i <= 4; i++)
                    if (lExecutedPlans[lExecutedPlans.Count - i].Count != 0)
                        bAllEmpty = false;
                if (bAllEmpty)
                    return true;
            }
            return false;
        }

        protected List<string> Plan(PartiallySpecifiedState pssCurrent, bool bPreconditionFailure, out bool bDeadEndReached, out State sChosen)
        {
            List<string> lPlan = null;
            List<Formula> lDeadends = null;
            sChosen = null;
            bDeadEndReached = false;
            DeadEndExistence isDeadEnd = pssCurrent.IsDeadEndExistenceAll(out lDeadends);
            if (isDeadEnd == DeadEndExistence.DeadEndTrue)
            {
                //Debug.WriteLine("dead end state is");
                //Debug.WriteLine(daedend);
                bDeadEndReached = true;
                return null;

            }
            if (isDeadEnd == DeadEndExistence.MaybeDeadEnd)
            // || daedend.Size == 2
            {
                lPlan = PlanToObserveDeadEnd(pssCurrent, lDeadends, bPreconditionFailure, out sChosen);
            }


            if (lPlan == null)
            {
                lPlan = Plan( pssCurrent, out sChosen);
            }


            return lPlan;
        }
        protected bool IsReasoningAction(string sAction)
        {
            if (sAction.StartsWith("merge") || sAction.StartsWith("refute") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagmerge"))
                return true;
            if (sAction.Contains("knowledgegain") || sAction.Contains("knowledgeloss"))
                return true;
            if (sAction.Contains("advanceoptions"))
                return true;
            if (!sAction.StartsWith("r"))
                return false;
            for (int i = 1; i < sAction.Length; i++)
                if (sAction[i] < '0' || sAction[i] > '9')
                    return false;
            return true;
        }
        protected void VerifyPlan(string sPath, string deadEndFile, List<string> lPlan)
        {
            Parser p = new Parser();
            Domain domain = p.ParseDomain(sPath + "Kd.pddl");
            Problem problem = p.ParseProblem(sPath + "Kp.pddl", deadEndFile, domain);
            State sInit = problem.GetInitialBelief().ChooseState(true);
            State sCurrent = sInit, sNext = null;
            for (int i = 0; i < lPlan.Count; i++)
            {
                string sAction = lPlan[i];
                sNext = sCurrent.Apply(sAction);
                if (sNext == null)
                {
                    Debug.WriteLine("BUGBUG");
                    sNext = sCurrent.Apply(sAction);
                    return;
                }
                sCurrent = sNext;
            }
            if (!problem.IsGoalState(sCurrent))
                Debug.WriteLine("Plan verification failed!");
        }

        protected List<string> FilterReasoningActions(List<string> lPlan)
        {
            List<string> lFiltered = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.StartsWith("merge") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagrefute") || sAction.StartsWith("tagmerge") || sAction.StartsWith("refute"))
                    continue;
                if (sAction.EndsWith("-t") || sAction.EndsWith("-f"))
                    lFiltered.Add(sAction.Substring(sAction.Length - 2));
                else if (sAction.Contains("-t "))
                    lFiltered.Add(sAction.Replace("-t ", " "));
                else if (sAction.Contains("-f "))
                    lFiltered.Add(sAction.Replace("-f ", " "));
                else
                    lFiltered.Add(sAction);
            }
            return lFiltered;
        }


        public static List<string> ManualSolve(Domain d, Problem p)
        {

            BFSSolver solver = new BFSSolver();

            List<Action> lActions = solver.ManualSolve(p, d, true);


            List<string> lActionNames = new List<string>();
            foreach (Action a in lActions)
            {
                if (a != null)
                    lActionNames.Add(a.Name.Replace("_", " "));
            }
            return lActionNames;
        }

        public static List<string> ManualSolve(string sPath)
        {
            Parser parser = new Parser();
            Domain dK = parser.ParseDomain(sPath + "Kd.pddl");
            Problem pK = parser.ParseProblem(sPath + "Kp.pddl", "", dK);

           
            return ManualSolve(dK,pK);
        }

        protected List<string> Plan(PartiallySpecifiedState pssCurrent, out State sChosen)
        {
            Debug.WriteLine("Started classical planning");
            List<string> lPlan = null;
            if (TryImmediatePlan)
            {
                lPlan = GetImmediatePlan(pssCurrent);
                if (lPlan != null)
                {
                    sChosen = null;
                    return lPlan;
                }
            }


            int cTags = 0;
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem( out cTags, out msModels);


            MemoryStream msPlan = null;

            if (!WriteAllKVariations || cTags == 1)
            {
                lPlan = RunPlanner(msModels, -1);
                if (lPlan == null)
                {
                    Debug.WriteLine("Classical planner failed");
                    //ManualSolve(sPath);
                    return null;
                }


            }
            

            return lPlan;
        }

        protected List<string> PlanWithClassicalDeadendDetection(PartiallySpecifiedState pssCurrent, out State sChosen, out bool bIsDeadend)
        {
            Debug.WriteLine("Started classical planning");
            List<string> lPlan = null;
            bIsDeadend = false;

            sChosen = null;



            bool bFoundSolvableState = false;

            while (!bFoundSolvableState)
            {
                bFoundSolvableState = true;
                int cTags = 0;
                MemoryStream msModels = null;
                sChosen = pssCurrent.WriteTaggedDomainAndProblem(out cTags, out msModels);

                if (sChosen == null)
                {
                    bIsDeadend = true;
                    return null;
                }

                

                lPlan = RunPlanner( msModels, -1);
                if (lPlan == null)
                {
                    if (pssCurrent.Hidden.Count() == 0)
                    {
                        bIsDeadend = true;
                        return null;
                    }
                    else
                    {
                        bFoundSolvableState = false;
                        pssCurrent.AddCurrentToDeadendTags();
                    }
                }
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
            {
                Debug.WriteLine("BUGBUG");
            }

#endif
            return lPlan;
        }




        public List<string> RunPlanner(MemoryStream msModel, int iIndex)
        {
            if(InfoLevel > 1)
                Console.WriteLine("Calling underlying classical planner");


#if PYTHONNET
            if(UPParser != null && UPClassicalPlanner != null)
            {
                using (Py.GIL())
                {

                    CPORPlanner.TraceListener.WriteLine("Starting python");

                    msModel.Position = 0;

                    StreamReader sr = new StreamReader(msModel);
                    CPORPlanner.TraceListener.WriteLine("Read string from stream");
                    string s = sr.ReadToEnd();
                   
                    int idx = s.LastIndexOf("(define");
                    

                    
                    CPORPlanner.TraceListener.WriteLine("index found " + idx);


                    string sModel = s.Substring(0, idx);
                    CPORPlanner.TraceListener.WriteLine("got model string, starts with " + sModel.Substring(0,10));

                    CPORPlanner.TraceListener.WriteLine("get problem string");

                    string sProblem = s.Substring(idx);
                    CPORPlanner.TraceListener.WriteLine("got problem string, starts with " + sProblem.Substring(0, 10));
                    sr.Close();

                    
                    StreamWriter swDomain = new StreamWriter("Kd.pddl");
                    swDomain.Write(sModel);
                    swDomain.Close();

                    StreamWriter swProblem = new StreamWriter("Kp.pddl");
                    swProblem.Write(sProblem);
                    swProblem.Close();






                    sModel = "Kd.pddl";
                    sProblem = "Kp.pddl";
                    

                    CPORPlanner.TraceListener.WriteLine("Converting string to pyobject");
                    PyObject pysDomain = sModel.ToPython();
                    PyObject pysProblem = sProblem.ToPython();

                    CPORPlanner.TraceListener.WriteLine("Calling parser");


                    //PyObject oProblem = UPParser.InvokeMethod("parse_problem_string", pysDomain, pysProblem);
                    PyObject oProblem = UPParser.InvokeMethod("parse_problem", pysDomain, pysProblem);

                    CPORPlanner.TraceListener.WriteLine("Parser done");

                    PyObject oResult = UPClassicalPlanner.InvokeMethod("solve", oProblem);

                    CPORPlanner.TraceListener.WriteLine("Planner done");

                    return null;
                }
            }
            else 
#endif
            if (Options.Planner == Planners.LocalFSP)
            {
                ForwardSearchPlanner fsp = new ForwardSearchPlanner(msModel);
                if (InfoLevel > 1)
                    Console.WriteLine("Calling ForwardSearchPlanner");
                List<string> lPlan = fsp.Plan();
                if (InfoLevel > 1)
                {
                    Console.WriteLine("ForwardSearchPlanner done. Plan:");
                    foreach (string s in lPlan)
                    {
                        Console.WriteLine(s);
                    }
                }
                return lPlan;
            }
            else if(Options.Planner == Planners.FFCS)
            {
                if (InfoLevel > 1)
                    Console.WriteLine("Calling FFCS");
                FF ff = new FF(msModel);
                List<string> lPlan = ff.Plan();
                return lPlan;
            }
            else
            {
                throw new NotImplementedException();
            }
        }
        protected List<string> Plan(PartiallySpecifiedState pssCurrent, Predicate pObserve, out State sChosen)
        {
           
            int cTags = 0;

            CompoundFormula cfGoal = new CompoundFormula("or");
            cfGoal.AddOperand(pssCurrent.Problem.Goal);
            if (pObserve != null)
            {
                cfGoal.AddOperand(pObserve);
            }
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem(cfGoal, out cTags, out msModels);

            MemoryStream msPlan = null;
            List<string> lPlan = null;
            lPlan = RunPlanner(msModels, -1);
            if (lPlan == null)
            {
                Debug.WriteLine("Classical solver failed");
                return null;
            }

            return lPlan;
        }


        protected List<string> Plan(PartiallySpecifiedState pssCurrent, PartiallySpecifiedState pssClosed, out State sChosen)
        {
            int cTags = 0;

            CompoundFormula cfGoal = new CompoundFormula("or");
            cfGoal.AddOperand(pssCurrent.Problem.Goal);
            if (pssClosed != null)
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (GroundedPredicate gp in pssClosed.Observed)
                {
                    if (!pssCurrent.Problem.InitiallyUnknown(gp) && !pssCurrent.Problem.Domain.AlwaysConstant(gp))
                    {
                        if (!pssCurrent.Observed.Contains(gp))
                            cfAnd.AddOperand(gp);
                    }
                }
                if (cfAnd.Operands.Count > 0)
                    cfGoal.AddOperand(cfAnd);
            }
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem(cfGoal, out cTags, out msModels);


            List<string> lPlan = null;
            lPlan = RunPlanner(msModels, -1);
            if (lPlan == null)
            {
                Debug.WriteLine("Classical solver failed");
                return null;
            }


            return lPlan;
        }


        protected List<string> GetImmediatePlan(PartiallySpecifiedState pssCurrent)
        {
            return null;
            List<string> lPlan = null;
            List<Action> lActuationActions = pssCurrent.Problem.Domain.GroundAllActuationActions(pssCurrent.Observed, true);
            foreach (Action a in lActuationActions)
            {
                PartiallySpecifiedState pssNext = pssCurrent.Apply(a, out Formula fObserve);
                if (pssNext != null && pssNext.IsGoalState())
                {
                    lPlan = new List<string>();
                    lPlan.Add(a.Name);
                    return lPlan;
                }
            }
            return null;
        }

        protected List<string> PlanToObserveDeadEnd(PartiallySpecifiedState pssCurrent, List<Formula> lMaybeDeadends, bool bPreconditionFailure, out State sChosen)
        {
            Debug.WriteLine("Started classical deadend aware planning");

            List<string> lPlan = null;
            if (TryImmediatePlan)
            {
                lPlan = GetImmediatePlan(pssCurrent);
                if (lPlan != null)
                {
                    sChosen = null;
                    return lPlan;
                }
            }


            int cTags = 0;
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblemDeadEnd(lMaybeDeadends, DeadendStrategy, bPreconditionFailure, out cTags, out msModels);

            MemoryStream msPlan = null;


            lPlan = RunPlanner(msModels, -1);
            if (lPlan == null)
            {
                Debug.WriteLine("Classical planner failed");
                //lPlan = ManualSolve(sPath);
                return null;
            }



            return lPlan;


        }

        public void SetClassicalPlanner(object planner)
        {
#if PYTHONNET
            CPORPlanner.TraceListener.WriteLine("SetClassicalPlanner");

            PythonEngine.Initialize();
            if (planner is PyObject pyplanner)
            {
                CPORPlanner.TraceListener.WriteLine("SetClassicalPlanner: planner not null");


                UPClassicalPlanner = pyplanner;
            }
            else
            {
                UPClassicalPlanner = null;
            }
#endif
        }

        public void SetParser(object parser)
        {
#if PYTHONNET
            CPORPlanner.TraceListener.WriteLine("SetParser");


            PythonEngine.Initialize();
            if(parser is PyObject pyparser)
            {
                CPORPlanner.TraceListener.WriteLine("SetParser: parser not null");


                UPParser = pyparser;
            }
            else
            {
                UPParser = null;
            }
#endif
        }

    }
}
