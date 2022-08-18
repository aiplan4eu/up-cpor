
using CPORLib.PlanningModel;
using System;
using System.Collections.Generic;
using System.Text;

namespace CPORLib.Tools
{
    public class ExecutionData
    {
        public bool FinalStateDeadend { get; set; }
        public bool InitialStateDeadend { get; set; }

        public int Observations { get; set; }
        public int Actions { get; set; }
        public int Planning { get; set; }
        public TimeSpan Time { get; set; }
        public Domain Domain { get; set; }
        public Problem Problem { get; set; }

        public bool SampleDeadendState { get; set; }
        public string Path { get; set; }
        public string DeadEndFile { get; set; }
        public string Exception { get; set; }
        public bool Failure { get { return Exception != ""; } }

        public Options.DeadendStrategies DeadendStrategy { get; set; }

        public ExecutionData(string sPath, string sDeadEndFile, Domain d, Problem p, Options.DeadendStrategies ds)
        {
            Domain = d;
            Problem = p;
            Path = sPath;
            DeadEndFile = sDeadEndFile;
            Exception = "";
            DeadendStrategy = ds;
            SampleDeadendState = false;
        }
    }
}
