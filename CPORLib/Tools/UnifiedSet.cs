using Microsoft.SolverFoundation.Services;
using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Runtime.InteropServices;
using System.Text;
using System.Transactions;

namespace CPORLib.Tools
{
    public class UnifiedSet<T> : ISet<T>
    {
        private List<ISet<T>> Sets;

        public UnifiedSet()
        {
            Sets = new List<ISet<T>>();
            Count = 0;
        }

        public UnifiedSet(ISet<T> s1, ISet<T> s2) : this()
        {
            Add(s1);
            Add(s2);
        }

        public void Add(ISet<T> s)
        {
            Sets.Add(s);
            Count += s.Count;
        }

        public int Count;
        

        public bool IsReadOnly => throw new NotImplementedException();

        int ICollection<T>.Count
        {
            get
            {
                return Count;
            }
        }

        public bool Add(T item)
        {
            throw new NotImplementedException();
        }

        public void Clear()
        {
            throw new NotImplementedException();
        }

        public bool Contains(T item)
        {
            foreach(ISet<T> s in Sets)
                if(s.Contains(item))
                    return true;
            return false;
        }

        public void CopyTo(T[] array, int arrayIndex)
        {
            throw new NotImplementedException();
        }

        public void ExceptWith(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public IEnumerator<T> GetEnumerator()
        {
            return new UnifiedSetEnumerator<T>(Sets);
        }

        public void IntersectWith(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool IsProperSubsetOf(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool IsProperSupersetOf(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool IsSubsetOf(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool IsSupersetOf(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool Overlaps(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public bool Remove(T item)
        {
            throw new NotImplementedException();
        }

        public bool SetEquals(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public void SymmetricExceptWith(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        public void UnionWith(IEnumerable<T> other)
        {
            throw new NotImplementedException();
        }

        void ICollection<T>.Add(T item)
        {
            throw new NotImplementedException();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return new UnifiedSetEnumerator<T>(Sets);
        }

        private class UnifiedSetEnumerator<T> : IEnumerator<T>
        {
            private IEnumerator<T> CurrentEnumerator;
            private int SetIndex;
            private List<ISet<T>> Sets;

            public UnifiedSetEnumerator(List<ISet<T>> sets)
            {
                Sets = sets;
                Reset();
            }


            public T Current
            {
               get
                {
                    return CurrentEnumerator.Current;
                }
                
            }

            object IEnumerator.Current => throw new NotImplementedException();

            public void Dispose()
            {
                
            }

            public bool MoveNext()
            {
                bool b = CurrentEnumerator.MoveNext();
                if(!b)
                {
                    if(SetIndex < Sets.Count - 1)
                    {
                        SetIndex++;
                        CurrentEnumerator = Sets[SetIndex].GetEnumerator();
                        return MoveNext();
                    }
                }
                return b;
            }

            public void Reset()
            {
                SetIndex = 0;
                CurrentEnumerator = Sets[0].GetEnumerator();

            }
        }
    }
}
