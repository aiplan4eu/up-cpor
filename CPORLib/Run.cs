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


        public static void RunPlanner(string sDomainFile, string sProblemFile, string sOutputFile, bool bOnline, bool bValidate = false)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, domain);
            Debug.WriteLine("Done reading domain and problem");

            Options.TagsCount = 2;
            //Options.SDR_OBS = true;


            if (bOnline)
            {
                Random rnd = new Random(0);
                //sdr.OnlineReplanning();
                int cIterations = 50, cSuccess = 0;
                    int idx = 0;
                for (int i = 0; i < cIterations; i++)
                {
                    SDRPlanner sdr = new SDRPlanner(domain, problem);
                    Console.WriteLine("Starting " + domain.Name);
                    while (!sdr.GoalReached)
                    {
                        //if (idx == 19)
                        //    Console.Write("*");
                        string sAction = sdr.GetAction();
                        if (sAction == null)
                            Console.Write("*");
                        string sObservation = null;
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
