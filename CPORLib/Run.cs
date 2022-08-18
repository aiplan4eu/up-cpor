using CPORLib.Algorithms;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;

namespace CPORLib
{
    public class Run
    {
        public static void RunPlanner(string sDomainFile, string sProblemFile, string sOutputPath, bool bOnline, int iTimePerProblem)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, domain);
            Debug.WriteLine("Done reading domain and problem");

            SDRPlanner.TagsCount = 2;
            SDRPlanner sdr = new SDRPlanner(sOutputPath, domain, problem, bOnline);
            sdr.Start();
        }
        

    }
}
