using CPORLib.Algorithms;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using CPORLib.Tools;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;

namespace CPORLib
{
    public class Run
    {

        public static void Main(string[] args)
        {
            //TestAll();
            //return;


            if (args.Length < 3)
            {
                Console.WriteLine("Usage: RunPlanner domain_file problem_file output_file [online/offline]");
            }
            else
            {
                string sDomainFile = args[0];
                string sProblemFile = args[1];
                string sOutputFile = args[2];
                bool bOnline = false;
                if (args.Length > 3)
                    bOnline = args[2] == "online";
                RunPlanner(sDomainFile
                    , sProblemFile,
                    sOutputFile,
                    bOnline);
            }
        }


        public static void TestHAdd(Domain d, Problem p)
        {
            int cExecutions = 1000;
            HAddHeuristic h = new HAddHeuristic(d, p);
            BeliefState bs = p.GetInitialBelief();
            Console.WriteLine("Testing " + p.Name);

            Console.WriteLine("Choosing states");

            List<State> states = new List<State>();
            for (int i = 0; i < cExecutions; i++)
            {
                State s = bs.ChooseState(true);
                states.Add(s);
                if (i % 100 == 0)
                    Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + i + "/" + cExecutions);

            }

            DateTime dtStart = DateTime.Now;
            Console.WriteLine("\n Computing hadd");

            double dSum = 0.0;

            for(int i = 0; i < cExecutions; i++)
            {
                State s = states[i];
                double cost = h.ComputeHAdd(s);
                dSum += cost;
                //if (i % 100 == 0)
                  //  Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + i + "/" + cExecutions);
            }

            DateTime dtEnd = DateTime.Now;
            Console.WriteLine();
            Console.WriteLine("Run " + cExecutions + " in " + (dtEnd - dtStart).TotalMilliseconds + ", avg = " + dSum / cExecutions);

        }

        public static void RunPlanner(string sDomainFile, string sProblemFile, string sOutputFile, bool bOnline, bool bValidate = false)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, domain);
            Debug.WriteLine("Done reading domain and problem");


            //TestHAdd(domain, problem);
            //return;

            Options.TagsCount = 2;
            //Options.SDR_OBS = true;


            if (bOnline)
            {
                Random rnd = new Random(0);
                //sdr.OnlineReplanning();
                int cIterations = 10, cSuccess = 0;
                    int idx = 0;
                for (int i = 0; i < cIterations; i++)
                {
                    SDRPlanner sdr = new SDRPlanner(domain, problem);
                    Simulator sim = new Simulator(domain, problem);
                    Console.WriteLine("Starting " + domain.Name);
                    while (!sim.GoalReached)
                    {
                        
                        string sAction = sdr.GetAction();
                        if (sAction == null)
                            Console.Write("*");
                        string sObservation = sim.Apply(sAction);
                        bool bResult = sdr.SetObservation(sObservation);
                        if (!bResult)
                        {
                            sObservation = "true";
                            if (rnd.NextDouble() < 0.5)
                                sObservation = "false";
                            bResult = sdr.SetObservation(sObservation);
                        }
                        Console.WriteLine(idx + ") Executed " + sAction + ", received " + sObservation);
                        idx++;
                        
                    }
                    cSuccess++;
                }
            }
            else
            {
                CPORPlanner cpor = new CPORPlanner(domain, problem);
                cpor.InfoLevel = 1;
                ConditionalPlanTreeNode n = cpor.OfflinePlanning();
                cpor.WritePlan(sOutputFile, n);

                if (bValidate)
                    if (!cpor.ValidatePlanGraph(n))
                        Console.WriteLine("Invalid plan");
            }
        }
        

    }
}
