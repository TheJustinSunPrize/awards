import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule2126 (p1966 : Prop) (h : p1966) : (p1966) := by
  classical
  tauto

theorem initial2126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1966) := by
  have source : ((m.theta 7 10) < t) := by
    simpa only [Triangle] using (m.range 7 10 (by decide)).2
  exact rule2126 (meaning t m 1966) source

theorem rule2127 (p1967 : Prop) (h : p1967) : (p1967) := by
  classical
  tauto

theorem initial2127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1967) := by
  have source : ((m.theta 8 10) < t) := by
    simpa only [Triangle] using (m.range 8 10 (by decide)).2
  exact rule2127 (meaning t m 1967) source

theorem rule2128 (p1968 : Prop) (h : p1968) : (p1968) := by
  classical
  tauto

theorem initial2128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1968) := by
  have source : ((m.theta 1 9) < t) := by
    simpa only [Triangle] using (m.range 1 9 (by decide)).2
  exact rule2128 (meaning t m 1968) source

theorem rule2129 (p1969 : Prop) (h : p1969) : (p1969) := by
  classical
  tauto

theorem initial2129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1969) := by
  have source : ((m.theta 0 8) < t) := by
    simpa only [Triangle] using (m.range 0 8 (by decide)).2
  exact rule2129 (meaning t m 1969) source

theorem rule2131 (p1971 : Prop) (h : p1971) : (p1971) := by
  classical
  tauto

theorem initial2131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1971) := by
  have source : ((m.theta 6 10) < t) := by
    simpa only [Triangle] using (m.range 6 10 (by decide)).2
  exact rule2131 (meaning t m 1971) source

theorem rule2133 (p1973 : Prop) (h : p1973) : (p1973) := by
  classical
  tauto

theorem initial2133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1973) := by
  have source : ((m.theta 2 10) < t) := by
    simpa only [Triangle] using (m.range 2 10 (by decide)).2
  exact rule2133 (meaning t m 1973) source

theorem rule2135 (p1975 : Prop) (h : p1975) : (p1975) := by
  classical
  tauto

theorem initial2135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1975) := by
  have source : ((m.theta 6 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 6 7 (by decide)).1
  exact rule2135 (meaning t m 1975) source

theorem rule2136 (p1976 : Prop) (h : p1976) : (p1976) := by
  classical
  tauto

theorem initial2136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1976) := by
  have source : ((m.theta 0 2) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 2 (by decide)).1
  exact rule2136 (meaning t m 1976) source

theorem rule2137 (p1977 : Prop) (h : p1977) : (p1977) := by
  classical
  tauto

theorem initial2137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1977) := by
  have source : ((m.theta 1 3) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 3 (by decide)).1
  exact rule2137 (meaning t m 1977) source

theorem rule2138 (p1978 : Prop) (h : p1978) : (p1978) := by
  classical
  tauto

theorem initial2138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1978) := by
  have source : ((m.theta 0 5) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 5 (by decide)).1
  exact rule2138 (meaning t m 1978) source

theorem rule2139 (p1979 : Prop) (h : p1979) : (p1979) := by
  classical
  tauto

theorem initial2139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1979) := by
  have source : ((m.theta 3 5) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 5 (by decide)).1
  exact rule2139 (meaning t m 1979) source

theorem rule2140 (p1980 : Prop) (h : p1980) : (p1980) := by
  classical
  tauto

theorem initial2140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1980) := by
  have source : ((m.theta 3 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 6 (by decide)).1
  exact rule2140 (meaning t m 1980) source

theorem rule2141 (p1981 : Prop) (h : p1981) : (p1981) := by
  classical
  tauto

theorem initial2141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1981) := by
  have source : ((m.theta 6 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 6 8 (by decide)).1
  exact rule2141 (meaning t m 1981) source

theorem rule2142 (p1982 : Prop) (h : p1982) : (p1982) := by
  classical
  tauto

theorem initial2142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1982) := by
  have source : ((m.theta 8 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 8 9 (by decide)).1
  exact rule2142 (meaning t m 1982) source

theorem rule2143 (p1983 : Prop) (h : p1983) : (p1983) := by
  classical
  tauto

theorem initial2143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1983) := by
  have source : ((m.theta 7 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 7 9 (by decide)).1
  exact rule2143 (meaning t m 1983) source

theorem rule2144 (p1984 : Prop) (h : p1984) : (p1984) := by
  classical
  tauto

theorem initial2144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1984) := by
  have source : ((m.theta 0 1) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 1 (by decide)).1
  exact rule2144 (meaning t m 1984) source

theorem rule2145 (p1985 : Prop) (h : p1985) : (p1985) := by
  classical
  tauto

theorem initial2145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1985) := by
  have source : ((m.theta 5 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 5 7 (by decide)).1
  exact rule2145 (meaning t m 1985) source

theorem rule2146 (p1986 : Prop) (h : p1986) : (p1986) := by
  classical
  tauto

theorem initial2146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1986) := by
  have source : ((m.theta 2 4) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 4 (by decide)).1
  exact rule2146 (meaning t m 1986) source

theorem rule2147 (p1987 : Prop) (h : p1987) : (p1987) := by
  classical
  tauto

theorem initial2147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1987) := by
  have source : ((m.theta 2 3) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 3 (by decide)).1
  exact rule2147 (meaning t m 1987) source

theorem rule2148 (p1988 : Prop) (h : p1988) : (p1988) := by
  classical
  tauto

theorem initial2148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1988) := by
  have source : ((m.theta 9 10) ≥ 0) := by
    simpa only [Triangle] using (m.range 9 10 (by decide)).1
  exact rule2148 (meaning t m 1988) source

theorem rule2149 (p1989 : Prop) (h : p1989) : (p1989) := by
  classical
  tauto

theorem initial2149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1989) := by
  have source : ((m.theta 1 5) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 5 (by decide)).1
  exact rule2149 (meaning t m 1989) source

theorem rule2150 (p1990 : Prop) (h : p1990) : (p1990) := by
  classical
  tauto

theorem initial2150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1990) := by
  have source : ((m.theta 5 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 5 6 (by decide)).1
  exact rule2150 (meaning t m 1990) source

theorem rule2151 (p1991 : Prop) (h : p1991) : (p1991) := by
  classical
  tauto

theorem initial2151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1991) := by
  have source : ((m.theta 0 3) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 3 (by decide)).1
  exact rule2151 (meaning t m 1991) source

theorem rule2152 (p1992 : Prop) (h : p1992) : (p1992) := by
  classical
  tauto

theorem initial2152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1992) := by
  have source : ((m.theta 1 2) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 2 (by decide)).1
  exact rule2152 (meaning t m 1992) source

theorem rule2153 (p1993 : Prop) (h : p1993) : (p1993) := by
  classical
  tauto

theorem initial2153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1993) := by
  have source : ((m.theta 3 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 8 (by decide)).1
  exact rule2153 (meaning t m 1993) source

theorem rule2154 (p1994 : Prop) (h : p1994) : (p1994) := by
  classical
  tauto

theorem initial2154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1994) := by
  have source : ((m.theta 3 4) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 4 (by decide)).1
  exact rule2154 (meaning t m 1994) source

theorem rule2155 (p1995 : Prop) (h : p1995) : (p1995) := by
  classical
  tauto

theorem initial2155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1995) := by
  have source : ((m.theta 1 4) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 4 (by decide)).1
  exact rule2155 (meaning t m 1995) source

theorem rule2156 (p1996 : Prop) (h : p1996) : (p1996) := by
  classical
  tauto

theorem initial2156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1996) := by
  have source : ((m.theta 3 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 7 (by decide)).1
  exact rule2156 (meaning t m 1996) source

theorem rule2157 (p1997 : Prop) (h : p1997) : (p1997) := by
  classical
  tauto

theorem initial2157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1997) := by
  have source : ((m.theta 4 5) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 5 (by decide)).1
  exact rule2157 (meaning t m 1997) source

theorem rule2158 (p1998 : Prop) (h : p1998) : (p1998) := by
  classical
  tauto

theorem initial2158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1998) := by
  have source : ((m.theta 7 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 7 8 (by decide)).1
  exact rule2158 (meaning t m 1998) source

theorem rule2159 (p1999 : Prop) (h : p1999) : (p1999) := by
  classical
  tauto

theorem initial2159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1999) := by
  have source : ((m.theta 6 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 6 9 (by decide)).1
  exact rule2159 (meaning t m 1999) source

theorem rule2160 (p2000 : Prop) (h : p2000) : (p2000) := by
  classical
  tauto

theorem initial2160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2000) := by
  have source : ((m.theta 0 4) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 4 (by decide)).1
  exact rule2160 (meaning t m 2000) source

theorem rule2161 (p2001 : Prop) (h : p2001) : (p2001) := by
  classical
  tauto

theorem initial2161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2001) := by
  have source : ((m.theta 5 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 5 8 (by decide)).1
  exact rule2161 (meaning t m 2001) source

theorem rule2162 (p2002 : Prop) (h : p2002) : (p2002) := by
  classical
  tauto

theorem initial2162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2002) := by
  have source : ((m.theta 2 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 6 (by decide)).1
  exact rule2162 (meaning t m 2002) source

theorem rule2163 (p2003 : Prop) (h : p2003) : (p2003) := by
  classical
  tauto

theorem initial2163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2003) := by
  have source : ((m.theta 0 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 6 (by decide)).1
  exact rule2163 (meaning t m 2003) source

theorem rule2164 (p2004 : Prop) (h : p2004) : (p2004) := by
  classical
  tauto

theorem initial2164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2004) := by
  have source : ((m.theta 1 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 7 (by decide)).1
  exact rule2164 (meaning t m 2004) source

theorem rule2165 (p2005 : Prop) (h : p2005) : (p2005) := by
  classical
  tauto

theorem initial2165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2005) := by
  have source : ((m.theta 4 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 6 (by decide)).1
  exact rule2165 (meaning t m 2005) source

theorem rule2166 (p2006 : Prop) (h : p2006) : (p2006) := by
  classical
  tauto

theorem initial2166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2006) := by
  have source : ((m.theta 2 5) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 5 (by decide)).1
  exact rule2166 (meaning t m 2006) source

theorem rule2167 (p2007 : Prop) (h : p2007) : (p2007) := by
  classical
  tauto

theorem initial2167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2007) := by
  have source : ((m.theta 4 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 8 (by decide)).1
  exact rule2167 (meaning t m 2007) source

theorem rule2168 (p2008 : Prop) (h : p2008) : (p2008) := by
  classical
  tauto

theorem initial2168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2008) := by
  have source : ((m.theta 2 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 7 (by decide)).1
  exact rule2168 (meaning t m 2008) source

theorem rule2169 (p2009 : Prop) (h : p2009) : (p2009) := by
  classical
  tauto

theorem initial2169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2009) := by
  have source : ((m.theta 0 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 8 (by decide)).1
  exact rule2169 (meaning t m 2009) source

theorem rule2170 (p2010 : Prop) (h : p2010) : (p2010) := by
  classical
  tauto

theorem initial2170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2010) := by
  have source : ((m.theta 4 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 7 (by decide)).1
  exact rule2170 (meaning t m 2010) source

theorem rule2171 (p2011 : Prop) (h : p2011) : (p2011) := by
  classical
  tauto

theorem initial2171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2011) := by
  have source : ((m.theta 5 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 5 9 (by decide)).1
  exact rule2171 (meaning t m 2011) source

theorem rule2172 (p2012 : Prop) (h : p2012) : (p2012) := by
  classical
  tauto

theorem initial2172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2012) := by
  have source : ((m.theta 4 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 9 (by decide)).1
  exact rule2172 (meaning t m 2012) source

theorem rule2173 (p2013 : Prop) (h : p2013) : (p2013) := by
  classical
  tauto

theorem initial2173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2013) := by
  have source : ((m.theta 2 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 9 (by decide)).1
  exact rule2173 (meaning t m 2013) source

theorem rule2174 (p2014 : Prop) (h : p2014) : (p2014) := by
  classical
  tauto

theorem initial2174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2014) := by
  have source : ((m.theta 6 10) ≥ 0) := by
    simpa only [Triangle] using (m.range 6 10 (by decide)).1
  exact rule2174 (meaning t m 2014) source

theorem rule2175 (p2015 : Prop) (h : p2015) : (p2015) := by
  classical
  tauto

theorem initial2175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2015) := by
  have source : ((m.theta 1 6) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 6 (by decide)).1
  exact rule2175 (meaning t m 2015) source

theorem rule2177 (p2017 : Prop) (h : p2017) : (p2017) := by
  classical
  tauto

theorem initial2177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2017) := by
  have source : ((m.theta 7 10) ≥ 0) := by
    simpa only [Triangle] using (m.range 7 10 (by decide)).1
  exact rule2177 (meaning t m 2017) source

theorem rule2178 (p2018 : Prop) (h : p2018) : (p2018) := by
  classical
  tauto

theorem initial2178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2018) := by
  have source : ((m.theta 2 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 2 8 (by decide)).1
  exact rule2178 (meaning t m 2018) source

theorem rule2179 (p2019 : Prop) (h : p2019) : (p2019) := by
  classical
  tauto

theorem initial2179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2019) := by
  have source : ((m.theta 4 10) ≥ 0) := by
    simpa only [Triangle] using (m.range 4 10 (by decide)).1
  exact rule2179 (meaning t m 2019) source

theorem rule2180 (p2020 : Prop) (h : p2020) : (p2020) := by
  classical
  tauto

theorem initial2180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2020) := by
  have source : ((m.theta 8 10) ≥ 0) := by
    simpa only [Triangle] using (m.range 8 10 (by decide)).1
  exact rule2180 (meaning t m 2020) source

theorem rule2181 (p2021 : Prop) (h : p2021) : (p2021) := by
  classical
  tauto

theorem initial2181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2021) := by
  have source : ((m.theta 0 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 9 (by decide)).1
  exact rule2181 (meaning t m 2021) source

theorem rule2182 (p2022 : Prop) (h : p2022) : (p2022) := by
  classical
  tauto

theorem initial2182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2022) := by
  have source : ((m.theta 0 7) ≥ 0) := by
    simpa only [Triangle] using (m.range 0 7 (by decide)).1
  exact rule2182 (meaning t m 2022) source

theorem rule2183 (p2023 : Prop) (h : p2023) : (p2023) := by
  classical
  tauto

theorem initial2183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2023) := by
  have source : ((m.theta 1 8) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 8 (by decide)).1
  exact rule2183 (meaning t m 2023) source

theorem rule2184 (p2024 : Prop) (h : p2024) : (p2024) := by
  classical
  tauto

theorem initial2184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2024) := by
  have source : ((m.theta 3 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 3 9 (by decide)).1
  exact rule2184 (meaning t m 2024) source

theorem rule2185 (p2025 : Prop) (h : p2025) : (p2025) := by
  classical
  tauto

theorem initial2185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2025) := by
  have source : ((m.theta 1 9) ≥ 0) := by
    simpa only [Triangle] using (m.range 1 9 (by decide)).1
  exact rule2185 (meaning t m 2025) source

theorem rule2186 (p25 p2026 : Prop) (h : (p25 ↔ (¬ p2026))) : (¬ p25) ∨ (¬ p2026) := by
  classical
  tauto

theorem initial2186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 25)) ∨ (¬ (meaning t m 2026)) := by
  have source := ElevenTheory.theory0 t
  exact rule2186 (meaning t m 25) (meaning t m 2026) source

theorem rule2188 (p2026 p2027 : Prop) (h : ((¬ p2026) ↔ (¬ p2027))) : (p2026) ∨ (¬ p2027) := by
  classical
  tauto

theorem initial2188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2026) ∨ (¬ (meaning t m 2027)) := by
  have source := ElevenTheory.theory1 t
  exact rule2188 (meaning t m 2026) (meaning t m 2027) source

theorem rule2190 (p1922 p2028 : Prop) (h : (p1922 ↔ (¬ p2028))) : (¬ p1922) ∨ (¬ p2028) := by
  classical
  tauto

theorem initial2190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1922)) ∨ (¬ (meaning t m 2028)) := by
  have source := ElevenTheory.theory2 t (m.theta 1 2)
  exact rule2190 (meaning t m 1922) (meaning t m 2028) source

theorem rule2192 (p1923 p2029 : Prop) (h : (p1923 ↔ (¬ p2029))) : (¬ p1923) ∨ (¬ p2029) := by
  classical
  tauto

theorem initial2192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1923)) ∨ (¬ (meaning t m 2029)) := by
  have source := ElevenTheory.theory3 t (m.theta 0 5)
  exact rule2192 (meaning t m 1923) (meaning t m 2029) source

theorem rule2194 (p1924 p2030 : Prop) (h : (p1924 ↔ (¬ p2030))) : (¬ p1924) ∨ (¬ p2030) := by
  classical
  tauto

theorem initial2194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1924)) ∨ (¬ (meaning t m 2030)) := by
  have source := ElevenTheory.theory4 t (m.theta 6 8)
  exact rule2194 (meaning t m 1924) (meaning t m 2030) source

theorem rule2196 (p1925 p2031 : Prop) (h : (p1925 ↔ (¬ p2031))) : (¬ p1925) ∨ (¬ p2031) := by
  classical
  tauto

theorem initial2196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1925)) ∨ (¬ (meaning t m 2031)) := by
  have source := ElevenTheory.theory5 t (m.theta 4 5)
  exact rule2196 (meaning t m 1925) (meaning t m 2031) source

theorem rule2198 (p1926 p2032 : Prop) (h : (p1926 ↔ (¬ p2032))) : (¬ p1926) ∨ (¬ p2032) := by
  classical
  tauto

theorem initial2198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1926)) ∨ (¬ (meaning t m 2032)) := by
  have source := ElevenTheory.theory6 t (m.theta 0 4)
  exact rule2198 (meaning t m 1926) (meaning t m 2032) source

theorem rule2200 (p1927 p2033 : Prop) (h : (p1927 ↔ (¬ p2033))) : (¬ p1927) ∨ (¬ p2033) := by
  classical
  tauto

theorem initial2200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1927)) ∨ (¬ (meaning t m 2033)) := by
  have source := ElevenTheory.theory7 t (m.theta 3 6)
  exact rule2200 (meaning t m 1927) (meaning t m 2033) source

theorem rule2202 (p1928 p2034 : Prop) (h : (p1928 ↔ (¬ p2034))) : (¬ p1928) ∨ (¬ p2034) := by
  classical
  tauto

theorem initial2202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1928)) ∨ (¬ (meaning t m 2034)) := by
  have source := ElevenTheory.theory8 t (m.theta 0 3)
  exact rule2202 (meaning t m 1928) (meaning t m 2034) source

theorem rule2204 (p1929 p2035 : Prop) (h : (p1929 ↔ (¬ p2035))) : (¬ p1929) ∨ (¬ p2035) := by
  classical
  tauto

theorem initial2204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1929)) ∨ (¬ (meaning t m 2035)) := by
  have source := ElevenTheory.theory9 t (m.theta 0 6)
  exact rule2204 (meaning t m 1929) (meaning t m 2035) source

theorem rule2206 (p1930 p2036 : Prop) (h : (p1930 ↔ (¬ p2036))) : (¬ p1930) ∨ (¬ p2036) := by
  classical
  tauto

theorem initial2206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1930)) ∨ (¬ (meaning t m 2036)) := by
  have source := ElevenTheory.theory10 t (m.theta 3 7)
  exact rule2206 (meaning t m 1930) (meaning t m 2036) source

theorem rule2208 (p1931 p2037 : Prop) (h : (p1931 ↔ (¬ p2037))) : (¬ p1931) ∨ (¬ p2037) := by
  classical
  tauto

theorem initial2208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1931)) ∨ (¬ (meaning t m 2037)) := by
  have source := ElevenTheory.theory11 t (m.theta 3 5)
  exact rule2208 (meaning t m 1931) (meaning t m 2037) source

theorem rule2210 (p1932 p2038 : Prop) (h : (p1932 ↔ (¬ p2038))) : (¬ p1932) ∨ (¬ p2038) := by
  classical
  tauto

theorem initial2210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1932)) ∨ (¬ (meaning t m 2038)) := by
  have source := ElevenTheory.theory12 t (m.theta 1 4)
  exact rule2210 (meaning t m 1932) (meaning t m 2038) source

theorem rule2212 (p1933 p2039 : Prop) (h : (p1933 ↔ (¬ p2039))) : (¬ p1933) ∨ (¬ p2039) := by
  classical
  tauto

theorem initial2212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1933)) ∨ (¬ (meaning t m 2039)) := by
  have source := ElevenTheory.theory13 t (m.theta 7 9)
  exact rule2212 (meaning t m 1933) (meaning t m 2039) source

theorem rule2214 (p1934 p2040 : Prop) (h : (p1934 ↔ (¬ p2040))) : (¬ p1934) ∨ (¬ p2040) := by
  classical
  tauto

theorem initial2214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1934)) ∨ (¬ (meaning t m 2040)) := by
  have source := ElevenTheory.theory14 t (m.theta 3 4)
  exact rule2214 (meaning t m 1934) (meaning t m 2040) source

theorem rule2216 (p1935 p2041 : Prop) (h : (p1935 ↔ (¬ p2041))) : (¬ p1935) ∨ (¬ p2041) := by
  classical
  tauto

theorem initial2216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1935)) ∨ (¬ (meaning t m 2041)) := by
  have source := ElevenTheory.theory15 t (m.theta 0 2)
  exact rule2216 (meaning t m 1935) (meaning t m 2041) source

theorem rule2218 (p1936 p2042 : Prop) (h : (p1936 ↔ (¬ p2042))) : (¬ p1936) ∨ (¬ p2042) := by
  classical
  tauto

theorem initial2218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1936)) ∨ (¬ (meaning t m 2042)) := by
  have source := ElevenTheory.theory16 t (m.theta 2 3)
  exact rule2218 (meaning t m 1936) (meaning t m 2042) source

theorem rule2220 (p1937 p2043 : Prop) (h : (p1937 ↔ (¬ p2043))) : (¬ p1937) ∨ (¬ p2043) := by
  classical
  tauto

theorem initial2220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1937)) ∨ (¬ (meaning t m 2043)) := by
  have source := ElevenTheory.theory17 t (m.theta 7 8)
  exact rule2220 (meaning t m 1937) (meaning t m 2043) source

theorem rule2222 (p1938 p2044 : Prop) (h : (p1938 ↔ (¬ p2044))) : (¬ p1938) ∨ (¬ p2044) := by
  classical
  tauto

theorem initial2222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1938)) ∨ (¬ (meaning t m 2044)) := by
  have source := ElevenTheory.theory18 t (m.theta 1 3)
  exact rule2222 (meaning t m 1938) (meaning t m 2044) source

theorem rule2224 (p1939 p2045 : Prop) (h : (p1939 ↔ (¬ p2045))) : (¬ p1939) ∨ (¬ p2045) := by
  classical
  tauto

theorem initial2224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1939)) ∨ (¬ (meaning t m 2045)) := by
  have source := ElevenTheory.theory19 t (m.theta 0 1)
  exact rule2224 (meaning t m 1939) (meaning t m 2045) source

theorem rule2226 (p1940 p2046 : Prop) (h : (p1940 ↔ (¬ p2046))) : (¬ p1940) ∨ (¬ p2046) := by
  classical
  tauto

theorem initial2226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1940)) ∨ (¬ (meaning t m 2046)) := by
  have source := ElevenTheory.theory20 t (m.theta 9 10)
  exact rule2226 (meaning t m 1940) (meaning t m 2046) source

theorem rule2228 (p1941 p2047 : Prop) (h : (p1941 ↔ (¬ p2047))) : (¬ p1941) ∨ (¬ p2047) := by
  classical
  tauto

theorem initial2228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1941)) ∨ (¬ (meaning t m 2047)) := by
  have source := ElevenTheory.theory21 t (m.theta 5 6)
  exact rule2228 (meaning t m 1941) (meaning t m 2047) source

theorem rule2230 (p1942 p2048 : Prop) (h : (p1942 ↔ (¬ p2048))) : (¬ p1942) ∨ (¬ p2048) := by
  classical
  tauto

theorem initial2230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1942)) ∨ (¬ (meaning t m 2048)) := by
  have source := ElevenTheory.theory22 t (m.theta 8 9)
  exact rule2230 (meaning t m 1942) (meaning t m 2048) source

theorem rule2232 (p1943 p2049 : Prop) (h : (p1943 ↔ (¬ p2049))) : (¬ p1943) ∨ (¬ p2049) := by
  classical
  tauto

theorem initial2232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1943)) ∨ (¬ (meaning t m 2049)) := by
  have source := ElevenTheory.theory23 t (m.theta 2 4)
  exact rule2232 (meaning t m 1943) (meaning t m 2049) source

theorem rule2234 (p1944 p2050 : Prop) (h : (p1944 ↔ (¬ p2050))) : (¬ p1944) ∨ (¬ p2050) := by
  classical
  tauto

theorem initial2234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1944)) ∨ (¬ (meaning t m 2050)) := by
  have source := ElevenTheory.theory24 t (m.theta 1 5)
  exact rule2234 (meaning t m 1944) (meaning t m 2050) source

theorem rule2236 (p1945 p2051 : Prop) (h : (p1945 ↔ (¬ p2051))) : (¬ p1945) ∨ (¬ p2051) := by
  classical
  tauto

theorem initial2236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1945)) ∨ (¬ (meaning t m 2051)) := by
  have source := ElevenTheory.theory25 t (m.theta 4 7)
  exact rule2236 (meaning t m 1945) (meaning t m 2051) source

theorem rule2238 (p1946 p2052 : Prop) (h : (p1946 ↔ (¬ p2052))) : (¬ p1946) ∨ (¬ p2052) := by
  classical
  tauto

theorem initial2238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1946)) ∨ (¬ (meaning t m 2052)) := by
  have source := ElevenTheory.theory26 t (m.theta 5 7)
  exact rule2238 (meaning t m 1946) (meaning t m 2052) source

theorem rule2240 (p1947 p2053 : Prop) (h : (p1947 ↔ (¬ p2053))) : (¬ p1947) ∨ (¬ p2053) := by
  classical
  tauto

theorem initial2240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1947)) ∨ (¬ (meaning t m 2053)) := by
  have source := ElevenTheory.theory27 t (m.theta 4 9)
  exact rule2240 (meaning t m 1947) (meaning t m 2053) source

theorem rule2242 (p1948 p2054 : Prop) (h : (p1948 ↔ (¬ p2054))) : (¬ p1948) ∨ (¬ p2054) := by
  classical
  tauto

theorem initial2242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1948)) ∨ (¬ (meaning t m 2054)) := by
  have source := ElevenTheory.theory28 t (m.theta 6 7)
  exact rule2242 (meaning t m 1948) (meaning t m 2054) source

theorem rule2244 (p1949 p2055 : Prop) (h : (p1949 ↔ (¬ p2055))) : (¬ p1949) ∨ (¬ p2055) := by
  classical
  tauto

theorem initial2244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1949)) ∨ (¬ (meaning t m 2055)) := by
  have source := ElevenTheory.theory29 t (m.theta 4 6)
  exact rule2244 (meaning t m 1949) (meaning t m 2055) source

theorem rule2246 (p1950 p2056 : Prop) (h : (p1950 ↔ (¬ p2056))) : (¬ p1950) ∨ (¬ p2056) := by
  classical
  tauto

theorem initial2246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1950)) ∨ (¬ (meaning t m 2056)) := by
  have source := ElevenTheory.theory30 t (m.theta 3 8)
  exact rule2246 (meaning t m 1950) (meaning t m 2056) source

theorem rule2248 (p1951 p2057 : Prop) (h : (p1951 ↔ (¬ p2057))) : (¬ p1951) ∨ (¬ p2057) := by
  classical
  tauto

theorem initial2248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1951)) ∨ (¬ (meaning t m 2057)) := by
  have source := ElevenTheory.theory31 t (m.theta 5 9)
  exact rule2248 (meaning t m 1951) (meaning t m 2057) source

theorem rule2250 (p1952 p2058 : Prop) (h : (p1952 ↔ (¬ p2058))) : (¬ p1952) ∨ (¬ p2058) := by
  classical
  tauto

theorem initial2250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1952)) ∨ (¬ (meaning t m 2058)) := by
  have source := ElevenTheory.theory32 t (m.theta 6 9)
  exact rule2250 (meaning t m 1952) (meaning t m 2058) source

theorem rule2252 (p1953 p2059 : Prop) (h : (p1953 ↔ (¬ p2059))) : (¬ p1953) ∨ (¬ p2059) := by
  classical
  tauto

theorem initial2252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1953)) ∨ (¬ (meaning t m 2059)) := by
  have source := ElevenTheory.theory33 t (m.theta 0 7)
  exact rule2252 (meaning t m 1953) (meaning t m 2059) source

theorem rule2254 (p1954 p2060 : Prop) (h : (p1954 ↔ (¬ p2060))) : (¬ p1954) ∨ (¬ p2060) := by
  classical
  tauto

theorem initial2254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1954)) ∨ (¬ (meaning t m 2060)) := by
  have source := ElevenTheory.theory34 t (m.theta 2 7)
  exact rule2254 (meaning t m 1954) (meaning t m 2060) source

theorem rule2256 (p1955 p2061 : Prop) (h : (p1955 ↔ (¬ p2061))) : (¬ p1955) ∨ (¬ p2061) := by
  classical
  tauto

theorem initial2256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1955)) ∨ (¬ (meaning t m 2061)) := by
  have source := ElevenTheory.theory35 t (m.theta 1 8)
  exact rule2256 (meaning t m 1955) (meaning t m 2061) source

theorem rule2258 (p1956 p2062 : Prop) (h : (p1956 ↔ (¬ p2062))) : (¬ p1956) ∨ (¬ p2062) := by
  classical
  tauto

theorem initial2258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1956)) ∨ (¬ (meaning t m 2062)) := by
  have source := ElevenTheory.theory36 t (m.theta 2 5)
  exact rule2258 (meaning t m 1956) (meaning t m 2062) source

theorem rule2260 (p1957 p2063 : Prop) (h : (p1957 ↔ (¬ p2063))) : (¬ p1957) ∨ (¬ p2063) := by
  classical
  tauto

theorem initial2260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1957)) ∨ (¬ (meaning t m 2063)) := by
  have source := ElevenTheory.theory37 t (m.theta 4 8)
  exact rule2260 (meaning t m 1957) (meaning t m 2063) source

theorem rule2262 (p1958 p2064 : Prop) (h : (p1958 ↔ (¬ p2064))) : (¬ p1958) ∨ (¬ p2064) := by
  classical
  tauto

theorem initial2262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1958)) ∨ (¬ (meaning t m 2064)) := by
  have source := ElevenTheory.theory38 t (m.theta 5 8)
  exact rule2262 (meaning t m 1958) (meaning t m 2064) source

theorem rule2264 (p1959 p2065 : Prop) (h : (p1959 ↔ (¬ p2065))) : (¬ p1959) ∨ (¬ p2065) := by
  classical
  tauto

theorem initial2264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1959)) ∨ (¬ (meaning t m 2065)) := by
  have source := ElevenTheory.theory39 t (m.theta 2 6)
  exact rule2264 (meaning t m 1959) (meaning t m 2065) source

theorem rule2266 (p1960 p2066 : Prop) (h : (p1960 ↔ (¬ p2066))) : (¬ p1960) ∨ (¬ p2066) := by
  classical
  tauto

theorem initial2266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1960)) ∨ (¬ (meaning t m 2066)) := by
  have source := ElevenTheory.theory40 t (m.theta 2 9)
  exact rule2266 (meaning t m 1960) (meaning t m 2066) source

theorem rule2268 (p1961 p2067 : Prop) (h : (p1961 ↔ (¬ p2067))) : (¬ p1961) ∨ (¬ p2067) := by
  classical
  tauto

theorem initial2268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1961)) ∨ (¬ (meaning t m 2067)) := by
  have source := ElevenTheory.theory41 t (m.theta 1 7)
  exact rule2268 (meaning t m 1961) (meaning t m 2067) source

theorem rule2270 (p1962 p2068 : Prop) (h : (p1962 ↔ (¬ p2068))) : (¬ p1962) ∨ (¬ p2068) := by
  classical
  tauto

theorem initial2270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1962)) ∨ (¬ (meaning t m 2068)) := by
  have source := ElevenTheory.theory42 t (m.theta 0 9)
  exact rule2270 (meaning t m 1962) (meaning t m 2068) source

theorem rule2272 (p1963 p2069 : Prop) (h : (p1963 ↔ (¬ p2069))) : (¬ p1963) ∨ (¬ p2069) := by
  classical
  tauto

theorem initial2272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1963)) ∨ (¬ (meaning t m 2069)) := by
  have source := ElevenTheory.theory43 t (m.theta 1 6)
  exact rule2272 (meaning t m 1963) (meaning t m 2069) source

theorem rule2274 (p1964 p2070 : Prop) (h : (p1964 ↔ (¬ p2070))) : (¬ p1964) ∨ (¬ p2070) := by
  classical
  tauto

theorem initial2274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1964)) ∨ (¬ (meaning t m 2070)) := by
  have source := ElevenTheory.theory44 t (m.theta 3 9)
  exact rule2274 (meaning t m 1964) (meaning t m 2070) source

theorem rule2278 (p1966 p2072 : Prop) (h : (p1966 ↔ (¬ p2072))) : (¬ p1966) ∨ (¬ p2072) := by
  classical
  tauto

theorem initial2278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1966)) ∨ (¬ (meaning t m 2072)) := by
  have source := ElevenTheory.theory46 t (m.theta 7 10)
  exact rule2278 (meaning t m 1966) (meaning t m 2072) source

theorem rule2280 (p1967 p2073 : Prop) (h : (p1967 ↔ (¬ p2073))) : (¬ p1967) ∨ (¬ p2073) := by
  classical
  tauto

theorem initial2280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1967)) ∨ (¬ (meaning t m 2073)) := by
  have source := ElevenTheory.theory47 t (m.theta 8 10)
  exact rule2280 (meaning t m 1967) (meaning t m 2073) source

theorem rule2282 (p1968 p2074 : Prop) (h : (p1968 ↔ (¬ p2074))) : (¬ p1968) ∨ (¬ p2074) := by
  classical
  tauto

theorem initial2282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1968)) ∨ (¬ (meaning t m 2074)) := by
  have source := ElevenTheory.theory48 t (m.theta 1 9)
  exact rule2282 (meaning t m 1968) (meaning t m 2074) source

theorem rule2284 (p1969 p2075 : Prop) (h : (p1969 ↔ (¬ p2075))) : (¬ p1969) ∨ (¬ p2075) := by
  classical
  tauto

theorem initial2284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1969)) ∨ (¬ (meaning t m 2075)) := by
  have source := ElevenTheory.theory49 t (m.theta 0 8)
  exact rule2284 (meaning t m 1969) (meaning t m 2075) source

theorem rule2288 (p1971 p2077 : Prop) (h : (p1971 ↔ (¬ p2077))) : (¬ p1971) ∨ (¬ p2077) := by
  classical
  tauto

theorem initial2288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1971)) ∨ (¬ (meaning t m 2077)) := by
  have source := ElevenTheory.theory51 t (m.theta 6 10)
  exact rule2288 (meaning t m 1971) (meaning t m 2077) source

theorem rule2292 (p1973 p2079 : Prop) (h : (p1973 ↔ (¬ p2079))) : (¬ p1973) ∨ (¬ p2079) := by
  classical
  tauto

theorem initial2292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1973)) ∨ (¬ (meaning t m 2079)) := by
  have source := ElevenTheory.theory53 t (m.theta 2 10)
  exact rule2292 (meaning t m 1973) (meaning t m 2079) source

theorem rule2296 (p1 p7 : Prop) : (¬ p1) ∨ ((p1 ∨ p7)) := by
  classical
  tauto

theorem initial2296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1)) ∨ (meaning t m 2081) := by
  exact rule2296 (meaning t m 1) (meaning t m 7)

theorem rule2297 (p1 p7 : Prop) : (¬ p7) ∨ ((p1 ∨ p7)) := by
  classical
  tauto

theorem initial2297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 7)) ∨ (meaning t m 2081) := by
  exact rule2297 (meaning t m 1) (meaning t m 7)

theorem rule2314 (p2081 p2082 : Prop) (h : (p2081 ↔ p2082)) : (¬ p2081) ∨ (p2082) := by
  classical
  tauto

theorem initial2314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2081)) ∨ (meaning t m 2082) := by
  have source := ElevenTheory.theory55 t (m.theta 0 8) (m.theta 0 9) (m.theta 8 9)
  exact rule2314 (meaning t m 2081) (meaning t m 2082) source

theorem rule2316 (p13 p19 : Prop) : (¬ p13) ∨ ((p13 ∨ p19)) := by
  classical
  tauto

theorem initial2316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 13)) ∨ (meaning t m 2091) := by
  exact rule2316 (meaning t m 13) (meaning t m 19)

theorem rule2317 (p13 p19 : Prop) : (¬ p19) ∨ ((p13 ∨ p19)) := by
  classical
  tauto

theorem initial2317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 19)) ∨ (meaning t m 2091) := by
  exact rule2317 (meaning t m 13) (meaning t m 19)

theorem rule2334 (p2091 p2092 : Prop) (h : (p2091 ↔ p2092)) : (¬ p2091) ∨ (p2092) := by
  classical
  tauto

theorem initial2334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2091)) ∨ (meaning t m 2092) := by
  have source := ElevenTheory.theory56 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 8)
  exact rule2334 (meaning t m 2091) (meaning t m 2092) source

theorem rule2336 (p2102 p2103 p2104 p2105 p2106 : Prop) : (¬ (p2102 ∧ p2103 ∧ p2104 ∧ p2105 ∧ p2106)) ∨ (p2102) := by
  classical
  tauto

theorem initial2336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2101)) ∨ (meaning t m 2102) := by
  exact rule2336 (meaning t m 2102) (meaning t m 2103) (meaning t m 2104) (meaning t m 2105) (meaning t m 2106)

theorem rule2337 (p2102 p2103 p2104 p2105 p2106 : Prop) : (¬ (p2102 ∧ p2103 ∧ p2104 ∧ p2105 ∧ p2106)) ∨ (p2103) := by
  classical
  tauto

theorem initial2337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2101)) ∨ (meaning t m 2103) := by
  exact rule2337 (meaning t m 2102) (meaning t m 2103) (meaning t m 2104) (meaning t m 2105) (meaning t m 2106)

theorem rule2338 (p2102 p2103 p2104 p2105 p2106 : Prop) : (¬ (p2102 ∧ p2103 ∧ p2104 ∧ p2105 ∧ p2106)) ∨ (p2104) := by
  classical
  tauto

theorem initial2338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2101)) ∨ (meaning t m 2104) := by
  exact rule2338 (meaning t m 2102) (meaning t m 2103) (meaning t m 2104) (meaning t m 2105) (meaning t m 2106)

theorem rule2343 (p2102 p2103 p2104 p2105 p2106 : Prop) : (p2103) ∨ (((¬ p2106) ∨ (¬ p2103) ∨ (¬ p2104) ∨ (¬ p2105) ∨ (¬ p2102))) := by
  classical
  tauto

theorem initial2343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2103) ∨ (meaning t m 2107) := by
  exact rule2343 (meaning t m 2102) (meaning t m 2103) (meaning t m 2104) (meaning t m 2105) (meaning t m 2106)

theorem rule2346 (p2102 p2103 p2104 p2105 p2106 : Prop) : (p2102) ∨ (((¬ p2106) ∨ (¬ p2103) ∨ (¬ p2104) ∨ (¬ p2105) ∨ (¬ p2102))) := by
  classical
  tauto

theorem initial2346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2102) ∨ (meaning t m 2107) := by
  exact rule2346 (meaning t m 2102) (meaning t m 2103) (meaning t m 2104) (meaning t m 2105) (meaning t m 2106)

theorem rule2348 (p2101 p2107 : Prop) (h : (p2101 ↔ (¬ p2107))) : (¬ p2101) ∨ (¬ p2107) := by
  classical
  tauto

theorem initial2348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2101)) ∨ (¬ (meaning t m 2107)) := by
  have source := ElevenTheory.theory57 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 8)
  exact rule2348 (meaning t m 2101) (meaning t m 2107) source

theorem rule2350 (p2098 p2109 p2110 p2111 p2112 : Prop) : (¬ (p2109 ∧ p2110 ∧ p2098 ∧ p2111 ∧ p2112)) ∨ (p2109) := by
  classical
  tauto

theorem initial2350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2108)) ∨ (meaning t m 2109) := by
  exact rule2350 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2351 (p2098 p2109 p2110 p2111 p2112 : Prop) : (¬ (p2109 ∧ p2110 ∧ p2098 ∧ p2111 ∧ p2112)) ∨ (p2110) := by
  classical
  tauto

theorem initial2351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2108)) ∨ (meaning t m 2110) := by
  exact rule2351 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2352 (p2098 p2109 p2110 p2111 p2112 : Prop) : (p2098) ∨ (¬ (p2109 ∧ p2110 ∧ p2098 ∧ p2111 ∧ p2112)) := by
  classical
  tauto

theorem initial2352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2098) ∨ (¬ (meaning t m 2108)) := by
  exact rule2352 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2358 (p2098 p2109 p2110 p2111 p2112 : Prop) : (p2109) ∨ (((¬ p2098) ∨ (¬ p2111) ∨ (¬ p2109) ∨ (¬ p2110) ∨ (¬ p2112))) := by
  classical
  tauto

theorem initial2358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2109) ∨ (meaning t m 2113) := by
  exact rule2358 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2359 (p2098 p2109 p2110 p2111 p2112 : Prop) : (p2110) ∨ (((¬ p2098) ∨ (¬ p2111) ∨ (¬ p2109) ∨ (¬ p2110) ∨ (¬ p2112))) := by
  classical
  tauto

theorem initial2359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2110) ∨ (meaning t m 2113) := by
  exact rule2359 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2360 (p2098 p2109 p2110 p2111 p2112 : Prop) : (p2112) ∨ (((¬ p2098) ∨ (¬ p2111) ∨ (¬ p2109) ∨ (¬ p2110) ∨ (¬ p2112))) := by
  classical
  tauto

theorem initial2360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2112) ∨ (meaning t m 2113) := by
  exact rule2360 (meaning t m 2098) (meaning t m 2109) (meaning t m 2110) (meaning t m 2111) (meaning t m 2112)

theorem rule2362 (p2108 p2113 : Prop) (h : (p2108 ↔ (¬ p2113))) : (¬ p2108) ∨ (¬ p2113) := by
  classical
  tauto

theorem initial2362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2108)) ∨ (¬ (meaning t m 2113)) := by
  have source := ElevenTheory.theory58 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 8)
  exact rule2362 (meaning t m 2108) (meaning t m 2113) source

theorem rule2364 (p2028 p2114 : Prop) (h : ((¬ p2028) ↔ (¬ p2114))) : (p2028) ∨ (¬ p2114) := by
  classical
  tauto

theorem initial2364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2028) ∨ (¬ (meaning t m 2114)) := by
  have source := ElevenTheory.theory59 t (m.theta 1 2)
  exact rule2364 (meaning t m 2028) (meaning t m 2114) source

theorem rule2366 (p26 p32 : Prop) : (¬ p26) ∨ ((p26 ∨ p32)) := by
  classical
  tauto

theorem initial2366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 26)) ∨ (meaning t m 2115) := by
  exact rule2366 (meaning t m 26) (meaning t m 32)

theorem rule2367 (p26 p32 : Prop) : (¬ p32) ∨ ((p26 ∨ p32)) := by
  classical
  tauto

theorem initial2367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 32)) ∨ (meaning t m 2115) := by
  exact rule2367 (meaning t m 26) (meaning t m 32)

theorem rule2384 (p2115 p2116 : Prop) (h : (p2115 ↔ p2116)) : (¬ p2115) ∨ (p2116) := by
  classical
  tauto

theorem initial2384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2115)) ∨ (meaning t m 2116) := by
  have source := ElevenTheory.theory60 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7)
  exact rule2384 (meaning t m 2115) (meaning t m 2116) source

theorem rule2386 (p38 p44 : Prop) : (¬ p38) ∨ ((p38 ∨ p44)) := by
  classical
  tauto

theorem initial2386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 38)) ∨ (meaning t m 2125) := by
  exact rule2386 (meaning t m 38) (meaning t m 44)

theorem rule2387 (p38 p44 : Prop) : (¬ p44) ∨ ((p38 ∨ p44)) := by
  classical
  tauto

theorem initial2387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 44)) ∨ (meaning t m 2125) := by
  exact rule2387 (meaning t m 38) (meaning t m 44)

theorem rule2404 (p2125 p2126 : Prop) (h : (p2125 ↔ p2126)) : (¬ p2125) ∨ (p2126) := by
  classical
  tauto

theorem initial2404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2125)) ∨ (meaning t m 2126) := by
  have source := ElevenTheory.theory61 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule2404 (meaning t m 2125) (meaning t m 2126) source

theorem rule2406 (p2136 p2137 p2138 p2139 p2140 : Prop) : (¬ (p2136 ∧ p2137 ∧ p2138 ∧ p2139 ∧ p2140)) ∨ (p2136) := by
  classical
  tauto

theorem initial2406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (meaning t m 2136) := by
  exact rule2406 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2407 (p2136 p2137 p2138 p2139 p2140 : Prop) : (¬ (p2136 ∧ p2137 ∧ p2138 ∧ p2139 ∧ p2140)) ∨ (p2137) := by
  classical
  tauto

theorem initial2407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (meaning t m 2137) := by
  exact rule2407 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2408 (p2136 p2137 p2138 p2139 p2140 : Prop) : (¬ (p2136 ∧ p2137 ∧ p2138 ∧ p2139 ∧ p2140)) ∨ (p2138) := by
  classical
  tauto

theorem initial2408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (meaning t m 2138) := by
  exact rule2408 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2409 (p2136 p2137 p2138 p2139 p2140 : Prop) : (¬ (p2136 ∧ p2137 ∧ p2138 ∧ p2139 ∧ p2140)) ∨ (p2139) := by
  classical
  tauto

theorem initial2409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (meaning t m 2139) := by
  exact rule2409 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2410 (p2136 p2137 p2138 p2139 p2140 : Prop) : (¬ (p2136 ∧ p2137 ∧ p2138 ∧ p2139 ∧ p2140)) ∨ (p2140) := by
  classical
  tauto

theorem initial2410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (meaning t m 2140) := by
  exact rule2410 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2412 (p2136 p2137 p2138 p2139 p2140 : Prop) : (p2139) ∨ (((¬ p2139) ∨ (¬ p2136) ∨ (¬ p2140) ∨ (¬ p2138) ∨ (¬ p2137))) := by
  classical
  tauto

theorem initial2412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2139) ∨ (meaning t m 2141) := by
  exact rule2412 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2413 (p2136 p2137 p2138 p2139 p2140 : Prop) : (p2136) ∨ (((¬ p2139) ∨ (¬ p2136) ∨ (¬ p2140) ∨ (¬ p2138) ∨ (¬ p2137))) := by
  classical
  tauto

theorem initial2413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2136) ∨ (meaning t m 2141) := by
  exact rule2413 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2416 (p2136 p2137 p2138 p2139 p2140 : Prop) : (p2137) ∨ (((¬ p2139) ∨ (¬ p2136) ∨ (¬ p2140) ∨ (¬ p2138) ∨ (¬ p2137))) := by
  classical
  tauto

theorem initial2416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2137) ∨ (meaning t m 2141) := by
  exact rule2416 (meaning t m 2136) (meaning t m 2137) (meaning t m 2138) (meaning t m 2139) (meaning t m 2140)

theorem rule2418 (p2135 p2141 : Prop) (h : (p2135 ↔ (¬ p2141))) : (¬ p2135) ∨ (¬ p2141) := by
  classical
  tauto

theorem initial2418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2135)) ∨ (¬ (meaning t m 2141)) := by
  have source := ElevenTheory.theory62 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule2418 (meaning t m 2135) (meaning t m 2141) source

theorem rule2420 (p2132 p2143 p2144 p2145 p2146 : Prop) : (¬ (p2143 ∧ p2144 ∧ p2132 ∧ p2145 ∧ p2146)) ∨ (p2143) := by
  classical
  tauto

theorem initial2420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2142)) ∨ (meaning t m 2143) := by
  exact rule2420 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2421 (p2132 p2143 p2144 p2145 p2146 : Prop) : (¬ (p2143 ∧ p2144 ∧ p2132 ∧ p2145 ∧ p2146)) ∨ (p2144) := by
  classical
  tauto

theorem initial2421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2142)) ∨ (meaning t m 2144) := by
  exact rule2421 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2422 (p2132 p2143 p2144 p2145 p2146 : Prop) : (p2132) ∨ (¬ (p2143 ∧ p2144 ∧ p2132 ∧ p2145 ∧ p2146)) := by
  classical
  tauto

theorem initial2422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2132) ∨ (¬ (meaning t m 2142)) := by
  exact rule2422 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2423 (p2132 p2143 p2144 p2145 p2146 : Prop) : (¬ (p2143 ∧ p2144 ∧ p2132 ∧ p2145 ∧ p2146)) ∨ (p2145) := by
  classical
  tauto

theorem initial2423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2142)) ∨ (meaning t m 2145) := by
  exact rule2423 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2424 (p2132 p2143 p2144 p2145 p2146 : Prop) : (¬ (p2143 ∧ p2144 ∧ p2132 ∧ p2145 ∧ p2146)) ∨ (p2146) := by
  classical
  tauto

theorem initial2424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2142)) ∨ (meaning t m 2146) := by
  exact rule2424 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2426 (p2132 p2143 p2144 p2145 p2146 : Prop) : (p2143) ∨ (((¬ p2143) ∨ (¬ p2144) ∨ (¬ p2132) ∨ (¬ p2145) ∨ (¬ p2146))) := by
  classical
  tauto

theorem initial2426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2143) ∨ (meaning t m 2147) := by
  exact rule2426 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2427 (p2132 p2143 p2144 p2145 p2146 : Prop) : (p2144) ∨ (((¬ p2143) ∨ (¬ p2144) ∨ (¬ p2132) ∨ (¬ p2145) ∨ (¬ p2146))) := by
  classical
  tauto

theorem initial2427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2144) ∨ (meaning t m 2147) := by
  exact rule2427 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2429 (p2132 p2143 p2144 p2145 p2146 : Prop) : (p2145) ∨ (((¬ p2143) ∨ (¬ p2144) ∨ (¬ p2132) ∨ (¬ p2145) ∨ (¬ p2146))) := by
  classical
  tauto

theorem initial2429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2145) ∨ (meaning t m 2147) := by
  exact rule2429 (meaning t m 2132) (meaning t m 2143) (meaning t m 2144) (meaning t m 2145) (meaning t m 2146)

theorem rule2432 (p2142 p2147 : Prop) (h : (p2142 ↔ (¬ p2147))) : (¬ p2142) ∨ (¬ p2147) := by
  classical
  tauto

theorem initial2432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2142)) ∨ (¬ (meaning t m 2147)) := by
  have source := ElevenTheory.theory63 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule2432 (meaning t m 2142) (meaning t m 2147) source

theorem rule2434 (p2029 p2148 : Prop) (h : ((¬ p2029) ↔ (¬ p2148))) : (p2029) ∨ (¬ p2148) := by
  classical
  tauto

theorem initial2434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2029) ∨ (¬ (meaning t m 2148)) := by
  have source := ElevenTheory.theory64 t (m.theta 0 5)
  exact rule2434 (meaning t m 2029) (meaning t m 2148) source

theorem rule2436 (p50 p56 : Prop) : (¬ p50) ∨ ((p50 ∨ p56)) := by
  classical
  tauto

theorem initial2436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 50)) ∨ (meaning t m 2149) := by
  exact rule2436 (meaning t m 50) (meaning t m 56)

theorem rule2437 (p50 p56 : Prop) : (¬ p56) ∨ ((p50 ∨ p56)) := by
  classical
  tauto

theorem initial2437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 56)) ∨ (meaning t m 2149) := by
  exact rule2437 (meaning t m 50) (meaning t m 56)

theorem rule2454 (p2149 p2150 : Prop) (h : (p2149 ↔ p2150)) : (¬ p2149) ∨ (p2150) := by
  classical
  tauto

theorem initial2454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2149)) ∨ (meaning t m 2150) := by
  have source := ElevenTheory.theory65 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6)
  exact rule2454 (meaning t m 2149) (meaning t m 2150) source

theorem rule2456 (p62 p68 : Prop) : (¬ p62) ∨ ((p62 ∨ p68)) := by
  classical
  tauto

theorem initial2456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 62)) ∨ (meaning t m 2159) := by
  exact rule2456 (meaning t m 62) (meaning t m 68)

theorem rule2457 (p62 p68 : Prop) : (¬ p68) ∨ ((p62 ∨ p68)) := by
  classical
  tauto

theorem initial2457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 68)) ∨ (meaning t m 2159) := by
  exact rule2457 (meaning t m 62) (meaning t m 68)

theorem rule2474 (p2159 p2160 : Prop) (h : (p2159 ↔ p2160)) : (¬ p2159) ∨ (p2160) := by
  classical
  tauto

theorem initial2474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2159)) ∨ (meaning t m 2160) := by
  have source := ElevenTheory.theory66 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 8)
  exact rule2474 (meaning t m 2159) (meaning t m 2160) source

theorem rule2476 (p2030 p2169 : Prop) (h : ((¬ p2030) ↔ (¬ p2169))) : (p2030) ∨ (¬ p2169) := by
  classical
  tauto

theorem initial2476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2030) ∨ (¬ (meaning t m 2169)) := by
  have source := ElevenTheory.theory67 t (m.theta 6 8)
  exact rule2476 (meaning t m 2030) (meaning t m 2169) source

theorem rule2478 (p74 p80 : Prop) : (¬ p74) ∨ ((p74 ∨ p80)) := by
  classical
  tauto

theorem initial2478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 74)) ∨ (meaning t m 2170) := by
  exact rule2478 (meaning t m 74) (meaning t m 80)

theorem rule2479 (p74 p80 : Prop) : (¬ p80) ∨ ((p74 ∨ p80)) := by
  classical
  tauto

theorem initial2479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 80)) ∨ (meaning t m 2170) := by
  exact rule2479 (meaning t m 74) (meaning t m 80)

theorem rule2496 (p2170 p2171 : Prop) (h : (p2170 ↔ p2171)) : (¬ p2170) ∨ (p2171) := by
  classical
  tauto

theorem initial2496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2170)) ∨ (meaning t m 2171) := by
  have source := ElevenTheory.theory68 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule2496 (meaning t m 2170) (meaning t m 2171) source

theorem rule2498 (p86 p92 : Prop) : (¬ p86) ∨ ((p86 ∨ p92)) := by
  classical
  tauto

theorem initial2498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 86)) ∨ (meaning t m 2180) := by
  exact rule2498 (meaning t m 86) (meaning t m 92)

theorem rule2499 (p86 p92 : Prop) : (¬ p92) ∨ ((p86 ∨ p92)) := by
  classical
  tauto

theorem initial2499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 92)) ∨ (meaning t m 2180) := by
  exact rule2499 (meaning t m 86) (meaning t m 92)

theorem rule2516 (p2180 p2181 : Prop) (h : (p2180 ↔ p2181)) : (¬ p2180) ∨ (p2181) := by
  classical
  tauto

theorem initial2516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2180)) ∨ (meaning t m 2181) := by
  have source := ElevenTheory.theory69 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule2516 (meaning t m 2180) (meaning t m 2181) source

theorem rule2518 (p2190 p2191 p2192 : Prop) (h : (¬ p2190) ∨ (¬ p2191) ∨ (¬ p2192)) : (¬ p2190) ∨ (¬ p2191) ∨ (¬ p2192) := by
  classical
  tauto

theorem initial2518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) := by
  have source := ElevenTheory.theory70 (m.theta 1 5) (m.theta 5 6) (m.theta 5 8)
  exact rule2518 (meaning t m 2190) (meaning t m 2191) (meaning t m 2192) source

theorem rule2519 (p98 p104 : Prop) : (¬ p98) ∨ ((p98 ∨ p104)) := by
  classical
  tauto

theorem initial2519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 98)) ∨ (meaning t m 2193) := by
  exact rule2519 (meaning t m 98) (meaning t m 104)

theorem rule2520 (p98 p104 : Prop) : (¬ p104) ∨ ((p98 ∨ p104)) := by
  classical
  tauto

theorem initial2520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 104)) ∨ (meaning t m 2193) := by
  exact rule2520 (meaning t m 98) (meaning t m 104)

theorem rule2537 (p2193 p2194 : Prop) (h : (p2193 ↔ p2194)) : (¬ p2193) ∨ (p2194) := by
  classical
  tauto

theorem initial2537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2193)) ∨ (meaning t m 2194) := by
  have source := ElevenTheory.theory71 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6)
  exact rule2537 (meaning t m 2193) (meaning t m 2194) source

theorem rule2539 (p2031 p2202 : Prop) (h : ((¬ p2031) ↔ (¬ p2202))) : (p2031) ∨ (¬ p2202) := by
  classical
  tauto

theorem initial2539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2031) ∨ (¬ (meaning t m 2202)) := by
  have source := ElevenTheory.theory72 t (m.theta 4 5)
  exact rule2539 (meaning t m 2031) (meaning t m 2202) source

theorem rule2541 (p110 p116 : Prop) : (¬ p110) ∨ ((p110 ∨ p116)) := by
  classical
  tauto

theorem initial2541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 110)) ∨ (meaning t m 2203) := by
  exact rule2541 (meaning t m 110) (meaning t m 116)

theorem rule2542 (p110 p116 : Prop) : (¬ p116) ∨ ((p110 ∨ p116)) := by
  classical
  tauto

theorem initial2542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 116)) ∨ (meaning t m 2203) := by
  exact rule2542 (meaning t m 110) (meaning t m 116)

theorem rule2559 (p2203 p2204 : Prop) (h : (p2203 ↔ p2204)) : (¬ p2203) ∨ (p2204) := by
  classical
  tauto

theorem initial2559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2203)) ∨ (meaning t m 2204) := by
  have source := ElevenTheory.theory73 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5)
  exact rule2559 (meaning t m 2203) (meaning t m 2204) source

theorem rule2561 (p122 p128 : Prop) : (¬ p122) ∨ ((p122 ∨ p128)) := by
  classical
  tauto

theorem initial2561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 122)) ∨ (meaning t m 2213) := by
  exact rule2561 (meaning t m 122) (meaning t m 128)

theorem rule2562 (p122 p128 : Prop) : (¬ p128) ∨ ((p122 ∨ p128)) := by
  classical
  tauto

theorem initial2562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 128)) ∨ (meaning t m 2213) := by
  exact rule2562 (meaning t m 122) (meaning t m 128)

theorem rule2579 (p2213 p2214 : Prop) (h : (p2213 ↔ p2214)) : (¬ p2213) ∨ (p2214) := by
  classical
  tauto

theorem initial2579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2213)) ∨ (meaning t m 2214) := by
  have source := ElevenTheory.theory74 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 8)
  exact rule2579 (meaning t m 2213) (meaning t m 2214) source

theorem rule2581 (p134 p140 : Prop) : (¬ p134) ∨ ((p134 ∨ p140)) := by
  classical
  tauto

theorem initial2581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 134)) ∨ (meaning t m 2223) := by
  exact rule2581 (meaning t m 134) (meaning t m 140)

theorem rule2582 (p134 p140 : Prop) : (¬ p140) ∨ ((p134 ∨ p140)) := by
  classical
  tauto

theorem initial2582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 140)) ∨ (meaning t m 2223) := by
  exact rule2582 (meaning t m 134) (meaning t m 140)

theorem rule2599 (p2223 p2224 : Prop) (h : (p2223 ↔ p2224)) : (¬ p2223) ∨ (p2224) := by
  classical
  tauto

theorem initial2599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2223)) ∨ (meaning t m 2224) := by
  have source := ElevenTheory.theory75 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5)
  exact rule2599 (meaning t m 2223) (meaning t m 2224) source

theorem rule2601 (p2032 p2233 : Prop) (h : ((¬ p2032) ↔ (¬ p2233))) : (p2032) ∨ (¬ p2233) := by
  classical
  tauto

theorem initial2601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2032) ∨ (¬ (meaning t m 2233)) := by
  have source := ElevenTheory.theory76 t (m.theta 0 4)
  exact rule2601 (meaning t m 2032) (meaning t m 2233) source

theorem rule2603 (p146 p152 : Prop) : (¬ p146) ∨ ((p146 ∨ p152)) := by
  classical
  tauto

theorem initial2603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 146)) ∨ (meaning t m 2234) := by
  exact rule2603 (meaning t m 146) (meaning t m 152)

theorem rule2604 (p146 p152 : Prop) : (¬ p152) ∨ ((p146 ∨ p152)) := by
  classical
  tauto

theorem initial2604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 152)) ∨ (meaning t m 2234) := by
  exact rule2604 (meaning t m 146) (meaning t m 152)

theorem rule2621 (p2234 p2235 : Prop) (h : (p2234 ↔ p2235)) : (¬ p2234) ∨ (p2235) := by
  classical
  tauto

theorem initial2621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2234)) ∨ (meaning t m 2235) := by
  have source := ElevenTheory.theory77 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule2621 (meaning t m 2234) (meaning t m 2235) source

theorem rule2623 (p2245 p2246 p2247 p2248 p2249 : Prop) : (¬ (p2245 ∧ p2246 ∧ p2247 ∧ p2248 ∧ p2249)) ∨ (p2245) := by
  classical
  tauto

theorem initial2623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (meaning t m 2245) := by
  exact rule2623 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2624 (p2245 p2246 p2247 p2248 p2249 : Prop) : (¬ (p2245 ∧ p2246 ∧ p2247 ∧ p2248 ∧ p2249)) ∨ (p2246) := by
  classical
  tauto

theorem initial2624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (meaning t m 2246) := by
  exact rule2624 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2625 (p2245 p2246 p2247 p2248 p2249 : Prop) : (¬ (p2245 ∧ p2246 ∧ p2247 ∧ p2248 ∧ p2249)) ∨ (p2247) := by
  classical
  tauto

theorem initial2625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (meaning t m 2247) := by
  exact rule2625 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2626 (p2245 p2246 p2247 p2248 p2249 : Prop) : (¬ (p2245 ∧ p2246 ∧ p2247 ∧ p2248 ∧ p2249)) ∨ (p2248) := by
  classical
  tauto

theorem initial2626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (meaning t m 2248) := by
  exact rule2626 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2627 (p2245 p2246 p2247 p2248 p2249 : Prop) : (¬ (p2245 ∧ p2246 ∧ p2247 ∧ p2248 ∧ p2249)) ∨ (p2249) := by
  classical
  tauto

theorem initial2627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (meaning t m 2249) := by
  exact rule2627 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2630 (p2245 p2246 p2247 p2248 p2249 : Prop) : (p2246) ∨ (((¬ p2249) ∨ (¬ p2246) ∨ (¬ p2247) ∨ (¬ p2245) ∨ (¬ p2248))) := by
  classical
  tauto

theorem initial2630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2246) ∨ (meaning t m 2250) := by
  exact rule2630 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2632 (p2245 p2246 p2247 p2248 p2249 : Prop) : (p2245) ∨ (((¬ p2249) ∨ (¬ p2246) ∨ (¬ p2247) ∨ (¬ p2245) ∨ (¬ p2248))) := by
  classical
  tauto

theorem initial2632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2245) ∨ (meaning t m 2250) := by
  exact rule2632 (meaning t m 2245) (meaning t m 2246) (meaning t m 2247) (meaning t m 2248) (meaning t m 2249)

theorem rule2635 (p2244 p2250 : Prop) (h : (p2244 ↔ (¬ p2250))) : (¬ p2244) ∨ (¬ p2250) := by
  classical
  tauto

theorem initial2635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2244)) ∨ (¬ (meaning t m 2250)) := by
  have source := ElevenTheory.theory78 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule2635 (meaning t m 2244) (meaning t m 2250) source

theorem rule2637 (p2241 p2252 p2253 p2254 p2255 : Prop) : (¬ (p2252 ∧ p2253 ∧ p2241 ∧ p2254 ∧ p2255)) ∨ (p2252) := by
  classical
  tauto

theorem initial2637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2251)) ∨ (meaning t m 2252) := by
  exact rule2637 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2638 (p2241 p2252 p2253 p2254 p2255 : Prop) : (¬ (p2252 ∧ p2253 ∧ p2241 ∧ p2254 ∧ p2255)) ∨ (p2253) := by
  classical
  tauto

theorem initial2638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2251)) ∨ (meaning t m 2253) := by
  exact rule2638 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2639 (p2241 p2252 p2253 p2254 p2255 : Prop) : (p2241) ∨ (¬ (p2252 ∧ p2253 ∧ p2241 ∧ p2254 ∧ p2255)) := by
  classical
  tauto

theorem initial2639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2241) ∨ (¬ (meaning t m 2251)) := by
  exact rule2639 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2640 (p2241 p2252 p2253 p2254 p2255 : Prop) : (¬ (p2252 ∧ p2253 ∧ p2241 ∧ p2254 ∧ p2255)) ∨ (p2254) := by
  classical
  tauto

theorem initial2640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2251)) ∨ (meaning t m 2254) := by
  exact rule2640 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2641 (p2241 p2252 p2253 p2254 p2255 : Prop) : (¬ (p2252 ∧ p2253 ∧ p2241 ∧ p2254 ∧ p2255)) ∨ (p2255) := by
  classical
  tauto

theorem initial2641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2251)) ∨ (meaning t m 2255) := by
  exact rule2641 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2643 (p2241 p2252 p2253 p2254 p2255 : Prop) : (p2253) ∨ (((¬ p2253) ∨ (¬ p2241) ∨ (¬ p2255) ∨ (¬ p2254) ∨ (¬ p2252))) := by
  classical
  tauto

theorem initial2643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2253) ∨ (meaning t m 2256) := by
  exact rule2643 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2647 (p2241 p2252 p2253 p2254 p2255 : Prop) : (p2252) ∨ (((¬ p2253) ∨ (¬ p2241) ∨ (¬ p2255) ∨ (¬ p2254) ∨ (¬ p2252))) := by
  classical
  tauto

theorem initial2647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2252) ∨ (meaning t m 2256) := by
  exact rule2647 (meaning t m 2241) (meaning t m 2252) (meaning t m 2253) (meaning t m 2254) (meaning t m 2255)

theorem rule2649 (p2251 p2256 : Prop) (h : (p2251 ↔ (¬ p2256))) : (¬ p2251) ∨ (¬ p2256) := by
  classical
  tauto

theorem initial2649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2251)) ∨ (¬ (meaning t m 2256)) := by
  have source := ElevenTheory.theory79 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule2649 (meaning t m 2251) (meaning t m 2256) source

theorem rule2651 (p158 p164 : Prop) : (¬ p158) ∨ ((p158 ∨ p164)) := by
  classical
  tauto

theorem initial2651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 158)) ∨ (meaning t m 2257) := by
  exact rule2651 (meaning t m 158) (meaning t m 164)

end SunPrize.SMT
