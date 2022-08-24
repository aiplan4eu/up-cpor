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
        public static void RunPlanner(string sDomainFile, string sProblemFile, bool bOnline)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, domain);
            Debug.WriteLine("Done reading domain and problem");

            Options.TagsCount = 2;


            if (bOnline)
            {
                SDRPlanner sdr = new SDRPlanner(domain, problem);
                sdr.OnlineReplanning();
            }
            else
            {
                CPORPlanner cpor = new CPORPlanner(domain, problem);
                cpor.Verbose = true;
                var n = cpor.OfflinePlanning();
                cpor.WritePlan("test.dot", n);
            }
        }
        

    }
}
