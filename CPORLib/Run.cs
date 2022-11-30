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
                SDRPlanner sdr = new SDRPlanner(domain, problem);
                sdr.OnlineReplanning();
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
