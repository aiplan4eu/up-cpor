using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace CPORLib.Tools
{
    public class StringStreamReader 
    {
        private StreamReader Reader;
        private string InputString;
        private int Index;

        public StringStreamReader(StreamReader sr)
        {
            Reader = sr;
        }
        public StringStreamReader(string sInput)
        {
            InputString = sInput;
            Index = 0;
        }
        public string ReadLine()
        {
            if(Reader == null)
            {
                string sLine = "";
                int i = 0;
                for (i = Index; i < InputString.Length; i++)
                {
                    if (InputString[i] == '\n')
                    {
                        Index = i + 1;
                        return sLine;
                    }
                    else
                    {
                        sLine += InputString[i];
                    }
                }
                Index = i;
                return sLine;
            }
            else
            {
                return Reader.ReadLine();
            }
        }

        public bool EndOfStream
        {
            get
            {
                if (Reader != null)
                    return Reader.EndOfStream;
                else
                    return Index == InputString.Length;
            }
        }

    }
}
