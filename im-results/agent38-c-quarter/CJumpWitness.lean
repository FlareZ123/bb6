import CJumpCore
namespace BB6Agent38
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

private theorem p0 : run 0 (some (5,0,1)) = some (5,0,1) := rfl

private theorem p1 : run 48849 (some (5,0,1)) = some (1099,50,0) := by
  have hp : path 1024 (5,0,1) = (48849, some (1099,50,0)) := by decide
  have hs : run 48849 (some (5,0,1)) = some (1099,50,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (5,0,1)
  have hc : run 48849 (some (5,0,1)) = run 48849 (run 0 (some (5,0,1))) := by
    simpa only [show 48849 + 0 = 48849 by decide] using run_add 48849 0 (some (5,0,1))
  rw [hc,p0,hs]

private theorem p2 : run 201678 (some (5,0,1)) = some (0,921,565) := by
  have hp : path 1024 (1099,50,0) = (152829, some (0,921,565)) := by decide
  have hs : run 152829 (some (1099,50,0)) = some (0,921,565) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (1099,50,0)
  have hc : run 201678 (some (5,0,1)) = run 152829 (run 48849 (some (5,0,1))) := by
    simpa only [show 152829 + 48849 = 201678 by decide] using run_add 152829 48849 (some (5,0,1))
  rw [hc,p1,hs]

private theorem p3 : run 466038 (some (5,0,1)) = some (0,1652,289) := by
  have hp : path 1024 (0,921,565) = (264360, some (0,1652,289)) := by decide
  have hs : run 264360 (some (0,921,565)) = some (0,1652,289) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,921,565)
  have hc : run 466038 (some (5,0,1)) = run 264360 (run 201678 (some (5,0,1))) := by
    simpa only [show 264360 + 201678 = 466038 by decide] using run_add 264360 201678 (some (5,0,1))
  rw [hc,p2,hs]

private theorem p4 : run 817846 (some (5,0,1)) = some (3452,663,3) := by
  have hp : path 1024 (0,1652,289) = (351808, some (3452,663,3)) := by decide
  have hs : run 351808 (some (0,1652,289)) = some (3452,663,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,1652,289)
  have hc : run 817846 (some (5,0,1)) = run 351808 (run 466038 (some (5,0,1))) := by
    simpa only [show 351808 + 466038 = 817846 by decide] using run_add 351808 466038 (some (5,0,1))
  rw [hc,p3,hs]

private theorem p5 : run 1234623 (some (5,0,1)) = some (0,2624,703) := by
  have hp : path 1024 (3452,663,3) = (416777, some (0,2624,703)) := by decide
  have hs : run 416777 (some (3452,663,3)) = some (0,2624,703) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (3452,663,3)
  have hc : run 1234623 (some (5,0,1)) = run 416777 (run 817846 (some (5,0,1))) := by
    simpa only [show 416777 + 817846 = 1234623 by decide] using run_add 416777 817846 (some (5,0,1))
  rw [hc,p4,hs]

private theorem p6 : run 1786860 (some (5,0,1)) = some (3399,1878,3) := by
  have hp : path 1024 (0,2624,703) = (552237, some (3399,1878,3)) := by decide
  have hs : run 552237 (some (0,2624,703)) = some (3399,1878,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,2624,703)
  have hc : run 1786860 (some (5,0,1)) = run 552237 (run 1234623 (some (5,0,1))) := by
    simpa only [show 552237 + 1234623 = 1786860 by decide] using run_add 552237 1234623 (some (5,0,1))
  rw [hc,p5,hs]

private theorem p7 : run 2466995 (some (5,0,1)) = some (5216,1571,0) := by
  have hp : path 1024 (3399,1878,3) = (680135, some (5216,1571,0)) := by decide
  have hs : run 680135 (some (3399,1878,3)) = some (5216,1571,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (3399,1878,3)
  have hc : run 2466995 (some (5,0,1)) = run 680135 (run 1786860 (some (5,0,1))) := by
    simpa only [show 680135 + 1786860 = 2466995 by decide] using run_add 680135 1786860 (some (5,0,1))
  rw [hc,p6,hs]

private theorem p8 : run 3266435 (some (5,0,1)) = some (0,2876,3812) := by
  have hp : path 1024 (5216,1571,0) = (799440, some (0,2876,3812)) := by decide
  have hs : run 799440 (some (5216,1571,0)) = some (0,2876,3812) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (5216,1571,0)
  have hc : run 3266435 (some (5,0,1)) = run 799440 (run 2466995 (some (5,0,1))) := by
    simpa only [show 799440 + 2466995 = 3266435 by decide] using run_add 799440 2466995 (some (5,0,1))
  rw [hc,p7,hs]

private theorem p9 : run 4127193 (some (5,0,1)) = some (1984,4383,3) := by
  have hp : path 1024 (0,2876,3812) = (860758, some (1984,4383,3)) := by decide
  have hs : run 860758 (some (0,2876,3812)) = some (1984,4383,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,2876,3812)
  have hc : run 4127193 (some (5,0,1)) = run 860758 (run 3266435 (some (5,0,1))) := by
    simpa only [show 860758 + 3266435 = 4127193 by decide] using run_add 860758 3266435 (some (5,0,1))
  rw [hc,p8,hs]

private theorem p10 : run 5009288 (some (5,0,1)) = some (2389,4762,0) := by
  have hp : path 1024 (1984,4383,3) = (882095, some (2389,4762,0)) := by decide
  have hs : run 882095 (some (1984,4383,3)) = some (2389,4762,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (1984,4383,3)
  have hc : run 5009288 (some (5,0,1)) = run 882095 (run 4127193 (some (5,0,1))) := by
    simpa only [show 882095 + 4127193 = 5009288 by decide] using run_add 882095 4127193 (some (5,0,1))
  rw [hc,p9,hs]

private theorem p11 : run 6038361 (some (5,0,1)) = some (8834,2131,3) := by
  have hp : path 1024 (2389,4762,0) = (1029073, some (8834,2131,3)) := by decide
  have hs : run 1029073 (some (2389,4762,0)) = some (8834,2131,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (2389,4762,0)
  have hc : run 6038361 (some (5,0,1)) = run 1029073 (run 5009288 (some (5,0,1))) := by
    simpa only [show 1029073 + 5009288 = 6038361 by decide] using run_add 1029073 5009288 (some (5,0,1))
  rw [hc,p10,hs]

private theorem p12 : run 7267282 (some (5,0,1)) = some (0,2557,9191) := by
  have hp : path 1024 (8834,2131,3) = (1228921, some (0,2557,9191)) := by decide
  have hs : run 1228921 (some (8834,2131,3)) = some (0,2557,9191) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (8834,2131,3)
  have hc : run 7267282 (some (5,0,1)) = run 1228921 (run 6038361 (some (5,0,1))) := by
    simpa only [show 1228921 + 6038361 = 7267282 by decide] using run_add 1228921 6038361 (some (5,0,1))
  rw [hc,p11,hs]

private theorem p13 : run 8616055 (some (5,0,1)) = some (4269,5622,0) := by
  have hp : path 1024 (0,2557,9191) = (1348773, some (4269,5622,0)) := by decide
  have hs : run 1348773 (some (0,2557,9191)) = some (4269,5622,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,2557,9191)
  have hc : run 8616055 (some (5,0,1)) = run 1348773 (run 7267282 (some (5,0,1))) := by
    simpa only [show 1348773 + 7267282 = 8616055 by decide] using run_add 1348773 7267282 (some (5,0,1))
  rw [hc,p12,hs]

private theorem p14 : run 9951324 (some (5,0,1)) = some (168,8271,3) := by
  have hp : path 1024 (4269,5622,0) = (1335269, some (168,8271,3)) := by decide
  have hs : run 1335269 (some (4269,5622,0)) = some (168,8271,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (4269,5622,0)
  have hc : run 9951324 (some (5,0,1)) = run 1335269 (run 8616055 (some (5,0,1))) := by
    simpa only [show 1335269 + 8616055 = 9951324 by decide] using run_add 1335269 8616055 (some (5,0,1))
  rw [hc,p13,hs]

private theorem p15 : run 11544012 (some (5,0,1)) = some (515,8705,0) := by
  have hp : path 1024 (168,8271,3) = (1592688, some (515,8705,0)) := by decide
  have hs : run 1592688 (some (168,8271,3)) = some (515,8705,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (168,8271,3)
  have hc : run 11544012 (some (5,0,1)) = run 1592688 (run 9951324 (some (5,0,1))) := by
    simpa only [show 1592688 + 9951324 = 11544012 by decide] using run_add 1592688 9951324 (some (5,0,1))
  rw [hc,p14,hs]

private theorem p16 : run 13104718 (some (5,0,1)) = some (12509,3300,0) := by
  have hp : path 1024 (515,8705,0) = (1560706, some (12509,3300,0)) := by decide
  have hs : run 1560706 (some (515,8705,0)) = some (12509,3300,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (515,8705,0)
  have hc : run 13104718 (some (5,0,1)) = run 1560706 (run 11544012 (some (5,0,1))) := by
    simpa only [show 1560706 + 11544012 = 13104718 by decide] using run_add 1560706 11544012 (some (5,0,1))
  rw [hc,p15,hs]

private theorem p17 : run 14821687 (some (5,0,1)) = some (17069,1618,0) := by
  have hp : path 1024 (12509,3300,0) = (1716969, some (17069,1618,0)) := by decide
  have hs : run 1716969 (some (12509,3300,0)) = some (17069,1618,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (12509,3300,0)
  have hc : run 14821687 (some (5,0,1)) = run 1716969 (run 13104718 (some (5,0,1))) := by
    simpa only [show 1716969 + 13104718 = 14821687 by decide] using run_add 1716969 13104718 (some (5,0,1))
  rw [hc,p16,hs]

private theorem p18 : run 16632699 (some (5,0,1)) = some (21089,203,0) := by
  have hp : path 1024 (17069,1618,0) = (1811012, some (21089,203,0)) := by decide
  have hs : run 1811012 (some (17069,1618,0)) = some (21089,203,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (17069,1618,0)
  have hc : run 16632699 (some (5,0,1)) = run 1811012 (run 14821687 (some (5,0,1))) := by
    simpa only [show 1811012 + 14821687 = 16632699 by decide] using run_add 1811012 14821687 (some (5,0,1))
  rw [hc,p17,hs]

private theorem p19 : run 18386769 (some (5,0,1)) = some (12075,5306,0) := by
  have hp : path 1024 (21089,203,0) = (1754070, some (12075,5306,0)) := by decide
  have hs : run 1754070 (some (21089,203,0)) = some (12075,5306,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (21089,203,0)
  have hc : run 18386769 (some (5,0,1)) = run 1754070 (run 16632699 (some (5,0,1))) := by
    simpa only [show 1754070 + 16632699 = 18386769 by decide] using run_add 1754070 16632699 (some (5,0,1))
  rw [hc,p18,hs]

private theorem p20 : run 20417513 (some (5,0,1)) = some (5494,9194,3) := by
  have hp : path 1024 (12075,5306,0) = (2030744, some (5494,9194,3)) := by decide
  have hs : run 2030744 (some (12075,5306,0)) = some (5494,9194,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (12075,5306,0)
  have hc : run 20417513 (some (5,0,1)) = run 2030744 (run 18386769 (some (5,0,1))) := by
    simpa only [show 2030744 + 18386769 = 20417513 by decide] using run_add 2030744 18386769 (some (5,0,1))
  rw [hc,p19,hs]

private theorem p21 : run 22508331 (some (5,0,1)) = some (19549,2770,0) := by
  have hp : path 1024 (5494,9194,3) = (2090818, some (19549,2770,0)) := by decide
  have hs : run 2090818 (some (5494,9194,3)) = some (19549,2770,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (5494,9194,3)
  have hc : run 22508331 (some (5,0,1)) = run 2090818 (run 20417513 (some (5,0,1))) := by
    simpa only [show 2090818 + 20417513 = 22508331 by decide] using run_add 2090818 20417513 (some (5,0,1))
  rw [hc,p20,hs]

private theorem p22 : run 24783153 (some (5,0,1)) = some (0,5751,14785) := by
  have hp : path 1024 (19549,2770,0) = (2274822, some (0,5751,14785)) := by decide
  have hs : run 2274822 (some (19549,2770,0)) = some (0,5751,14785) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (19549,2770,0)
  have hc : run 24783153 (some (5,0,1)) = run 2274822 (run 22508331 (some (5,0,1))) := by
    simpa only [show 2274822 + 22508331 = 24783153 by decide] using run_add 2274822 22508331 (some (5,0,1))
  rw [hc,p21,hs]

private theorem p23 : run 27063673 (some (5,0,1)) = some (16164,5659,3) := by
  have hp : path 1024 (0,5751,14785) = (2280520, some (16164,5659,3)) := by decide
  have hs : run 2280520 (some (0,5751,14785)) = some (16164,5659,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,5751,14785)
  have hc : run 27063673 (some (5,0,1)) = run 2280520 (run 24783153 (some (5,0,1))) := by
    simpa only [show 2280520 + 24783153 = 27063673 by decide] using run_add 2280520 24783153 (some (5,0,1))
  rw [hc,p22,hs]

private theorem p24 : run 29402862 (some (5,0,1)) = some (4264,12203,3) := by
  have hp : path 1024 (16164,5659,3) = (2339189, some (4264,12203,3)) := by decide
  have hs : run 2339189 (some (16164,5659,3)) = some (4264,12203,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (16164,5659,3)
  have hc : run 29402862 (some (5,0,1)) = run 2339189 (run 27063673 (some (5,0,1))) := by
    simpa only [show 2339189 + 27063673 = 29402862 by decide] using run_add 2339189 27063673 (some (5,0,1))
  rw [hc,p23,hs]

private theorem p25 : run 31744890 (some (5,0,1)) = some (5308,12268,3) := by
  have hp : path 1024 (4264,12203,3) = (2342028, some (5308,12268,3)) := by decide
  have hs : run 2342028 (some (4264,12203,3)) = some (5308,12268,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (4264,12203,3)
  have hc : run 31744890 (some (5,0,1)) = run 2342028 (run 29402862 (some (5,0,1))) := by
    simpa only [show 2342028 + 29402862 = 31744890 by decide] using run_add 2342028 29402862 (some (5,0,1))
  rw [hc,p24,hs]

private theorem p26 : run 34325827 (some (5,0,1)) = some (3372,13828,3) := by
  have hp : path 1024 (5308,12268,3) = (2580937, some (3372,13828,3)) := by decide
  have hs : run 2580937 (some (5308,12268,3)) = some (3372,13828,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (5308,12268,3)
  have hc : run 34325827 (some (5,0,1)) = run 2580937 (run 31744890 (some (5,0,1))) := by
    simpa only [show 2580937 + 31744890 = 34325827 by decide] using run_add 2580937 31744890 (some (5,0,1))
  rw [hc,p25,hs]

private theorem p27 : run 37024643 (some (5,0,1)) = some (0,9559,13105) := by
  have hp : path 1024 (3372,13828,3) = (2698816, some (0,9559,13105)) := by decide
  have hs : run 2698816 (some (3372,13828,3)) = some (0,9559,13105) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (3372,13828,3)
  have hc : run 37024643 (some (5,0,1)) = run 2698816 (run 34325827 (some (5,0,1))) := by
    simpa only [show 2698816 + 34325827 = 37024643 by decide] using run_add 2698816 34325827 (some (5,0,1))
  rw [hc,p26,hs]

private theorem p28 : run 39828773 (some (5,0,1)) = some (0,5397,22615) := by
  have hp : path 1024 (0,9559,13105) = (2804130, some (0,5397,22615)) := by decide
  have hs : run 2804130 (some (0,9559,13105)) = some (0,5397,22615) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,9559,13105)
  have hc : run 39828773 (some (5,0,1)) = run 2804130 (run 37024643 (some (5,0,1))) := by
    simpa only [show 2804130 + 37024643 = 39828773 by decide] using run_add 2804130 37024643 (some (5,0,1))
  rw [hc,p27,hs]

private theorem p29 : run 42659445 (some (5,0,1)) = some (20460,7059,3) := by
  have hp : path 1024 (0,5397,22615) = (2830672, some (20460,7059,3)) := by decide
  have hs : run 2830672 (some (0,5397,22615)) = some (20460,7059,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,5397,22615)
  have hc : run 42659445 (some (5,0,1)) = run 2830672 (run 39828773 (some (5,0,1))) := by
    simpa only [show 2830672 + 39828773 = 42659445 by decide] using run_add 2830672 39828773 (some (5,0,1))
  rw [hc,p28,hs]

private theorem p30 : run 45673528 (some (5,0,1)) = some (0,13380,9013) := by
  have hp : path 1024 (20460,7059,3) = (3014083, some (0,13380,9013)) := by decide
  have hs : run 3014083 (some (20460,7059,3)) = some (0,13380,9013) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (20460,7059,3)
  have hc : run 45673528 (some (5,0,1)) = run 3014083 (run 42659445 (some (5,0,1))) := by
    simpa only [show 3014083 + 42659445 = 45673528 by decide] using run_add 3014083 42659445 (some (5,0,1))
  rw [hc,p29,hs]

private theorem p31 : run 48893062 (some (5,0,1)) = some (0,13232,10507) := by
  have hp : path 1024 (0,13380,9013) = (3219534, some (0,13232,10507)) := by decide
  have hs : run 3219534 (some (0,13380,9013)) = some (0,13232,10507) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,13380,9013)
  have hc : run 48893062 (some (5,0,1)) = run 3219534 (run 45673528 (some (5,0,1))) := by
    simpa only [show 3219534 + 45673528 = 48893062 by decide] using run_add 3219534 45673528 (some (5,0,1))
  rw [hc,p30,hs]

private theorem p32 : run 52149910 (some (5,0,1)) = some (0,6875,24431) := by
  have hp : path 1024 (0,13232,10507) = (3256848, some (0,6875,24431)) := by decide
  have hs : run 3256848 (some (0,13232,10507)) = some (0,6875,24431) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,13232,10507)
  have hc : run 52149910 (some (5,0,1)) = run 3256848 (run 48893062 (some (5,0,1))) := by
    simpa only [show 3256848 + 48893062 = 52149910 by decide] using run_add 3256848 48893062 (some (5,0,1))
  rw [hc,p31,hs]

private theorem p33 : run 55356688 (some (5,0,1)) = some (0,9125,21135) := by
  have hp : path 1024 (0,6875,24431) = (3206778, some (0,9125,21135)) := by decide
  have hs : run 3206778 (some (0,6875,24431)) = some (0,9125,21135) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,6875,24431)
  have hc : run 55356688 (some (5,0,1)) = run 3206778 (run 52149910 (some (5,0,1))) := by
    simpa only [show 3206778 + 52149910 = 55356688 by decide] using run_add 3206778 52149910 (some (5,0,1))
  rw [hc,p32,hs]

private theorem p34 : run 58753196 (some (5,0,1)) = some (0,18341,3905) := by
  have hp : path 1024 (0,9125,21135) = (3396508, some (0,18341,3905)) := by decide
  have hs : run 3396508 (some (0,9125,21135)) = some (0,18341,3905) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,9125,21135)
  have hc : run 58753196 (some (5,0,1)) = run 3396508 (run 55356688 (some (5,0,1))) := by
    simpa only [show 3396508 + 55356688 = 58753196 by decide] using run_add 3396508 55356688 (some (5,0,1))
  rw [hc,p33,hs]

private theorem p35 : run 62309417 (some (5,0,1)) = some (0,10748,20293) := by
  have hp : path 1024 (0,18341,3905) = (3556221, some (0,10748,20293)) := by decide
  have hs : run 3556221 (some (0,18341,3905)) = some (0,10748,20293) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,18341,3905)
  have hc : run 62309417 (some (5,0,1)) = run 3556221 (run 58753196 (some (5,0,1))) := by
    simpa only [show 3556221 + 58753196 = 62309417 by decide] using run_add 3556221 58753196 (some (5,0,1))
  rw [hc,p34,hs]

private theorem p36 : run 66085954 (some (5,0,1)) = some (0,12075,18827) := by
  have hp : path 1024 (0,10748,20293) = (3776537, some (0,12075,18827)) := by decide
  have hs : run 3776537 (some (0,10748,20293)) = some (0,12075,18827) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,10748,20293)
  have hc : run 66085954 (some (5,0,1)) = run 3776537 (run 62309417 (some (5,0,1))) := by
    simpa only [show 3776537 + 62309417 = 66085954 by decide] using run_add 3776537 62309417 (some (5,0,1))
  rw [hc,p35,hs]

private theorem p37 : run 69513874 (some (5,0,1)) = some (11355,16410,0) := by
  have hp : path 1024 (0,12075,18827) = (3427920, some (11355,16410,0)) := by decide
  have hs : run 3427920 (some (0,12075,18827)) = some (11355,16410,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,12075,18827)
  have hc : run 69513874 (some (5,0,1)) = run 3427920 (run 66085954 (some (5,0,1))) := by
    simpa only [show 3427920 + 66085954 = 69513874 by decide] using run_add 3427920 66085954 (some (5,0,1))
  rw [hc,p36,hs]

private theorem p38 : run 73558211 (some (5,0,1)) = some (0,18448,8475) := by
  have hp : path 1024 (11355,16410,0) = (4044337, some (0,18448,8475)) := by decide
  have hs : run 4044337 (some (11355,16410,0)) = some (0,18448,8475) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (11355,16410,0)
  have hc : run 73558211 (some (5,0,1)) = run 4044337 (run 69513874 (some (5,0,1))) := by
    simpa only [show 4044337 + 69513874 = 73558211 by decide] using run_add 4044337 69513874 (some (5,0,1))
  rw [hc,p37,hs]

private theorem p39 : run 77420283 (some (5,0,1)) = some (22341,12106,0) := by
  have hp : path 1024 (0,18448,8475) = (3862072, some (22341,12106,0)) := by decide
  have hs : run 3862072 (some (0,18448,8475)) = some (22341,12106,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,18448,8475)
  have hc : run 77420283 (some (5,0,1)) = run 3862072 (run 73558211 (some (5,0,1))) := by
    simpa only [show 3862072 + 73558211 = 77420283 by decide] using run_add 3862072 73558211 (some (5,0,1))
  rw [hc,p38,hs]

private theorem p40 : run 81241719 (some (5,0,1)) = some (17060,15339,3) := by
  have hp : path 1024 (22341,12106,0) = (3821436, some (17060,15339,3)) := by decide
  have hs : run 3821436 (some (22341,12106,0)) = some (17060,15339,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (22341,12106,0)
  have hc : run 81241719 (some (5,0,1)) = run 3821436 (run 77420283 (some (5,0,1))) := by
    simpa only [show 3821436 + 77420283 = 81241719 by decide] using run_add 3821436 77420283 (some (5,0,1))
  rw [hc,p39,hs]

private theorem p41 : run 85263672 (some (5,0,1)) = some (0,7996,32939) := by
  have hp : path 1024 (17060,15339,3) = (4021953, some (0,7996,32939)) := by decide
  have hs : run 4021953 (some (17060,15339,3)) = some (0,7996,32939) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (17060,15339,3)
  have hc : run 85263672 (some (5,0,1)) = run 4021953 (run 81241719 (some (5,0,1))) := by
    simpa only [show 4021953 + 81241719 = 85263672 by decide] using run_add 4021953 81241719 (some (5,0,1))
  rw [hc,p40,hs]

private theorem p42 : run 89570205 (some (5,0,1)) = some (0,1700,46725) := by
  have hp : path 1024 (0,7996,32939) = (4306533, some (0,1700,46725)) := by decide
  have hs : run 4306533 (some (0,7996,32939)) = some (0,1700,46725) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,7996,32939)
  have hc : run 89570205 (some (5,0,1)) = run 4306533 (run 85263672 (some (5,0,1))) := by
    simpa only [show 4306533 + 85263672 = 89570205 by decide] using run_add 4306533 85263672 (some (5,0,1))
  rw [hc,p41,hs]

private theorem p43 : run 93882824 (some (5,0,1)) = some (41669,4820,0) := by
  have hp : path 1024 (0,1700,46725) = (4312619, some (41669,4820,0)) := by decide
  have hs : run 4312619 (some (0,1700,46725)) = some (41669,4820,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,1700,46725)
  have hc : run 93882824 (some (5,0,1)) = run 4312619 (run 89570205 (some (5,0,1))) := by
    simpa only [show 4312619 + 89570205 = 93882824 by decide] using run_add 4312619 89570205 (some (5,0,1))
  rw [hc,p42,hs]

private theorem p44 : run 98382422 (some (5,0,1)) = some (12393,20059,0) := by
  have hp : path 1024 (41669,4820,0) = (4499598, some (12393,20059,0)) := by decide
  have hs : run 4499598 (some (41669,4820,0)) = some (12393,20059,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (41669,4820,0)
  have hc : run 98382422 (some (5,0,1)) = run 4499598 (run 93882824 (some (5,0,1))) := by
    simpa only [show 4499598 + 93882824 = 98382422 by decide] using run_add 4499598 93882824 (some (5,0,1))
  rw [hc,p43,hs]

private theorem p45 : run 102869987 (some (5,0,1)) = some (18327,17680,0) := by
  have hp : path 1024 (12393,20059,0) = (4487565, some (18327,17680,0)) := by decide
  have hs : run 4487565 (some (12393,20059,0)) = some (18327,17680,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (12393,20059,0)
  have hc : run 102869987 (some (5,0,1)) = run 4487565 (run 98382422 (some (5,0,1))) := by
    simpa only [show 4487565 + 98382422 = 102869987 by decide] using run_add 4487565 98382422 (some (5,0,1))
  rw [hc,p44,hs]

private theorem p46 : run 107667673 (some (5,0,1)) = some (0,19676,15533) := by
  have hp : path 1024 (18327,17680,0) = (4797686, some (0,19676,15533)) := by decide
  have hs : run 4797686 (some (18327,17680,0)) = some (0,19676,15533) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (18327,17680,0)
  have hc : run 107667673 (some (5,0,1)) = run 4797686 (run 102869987 (some (5,0,1))) := by
    simpa only [show 4797686 + 102869987 = 107667673 by decide] using run_add 4797686 102869987 (some (5,0,1))
  rw [hc,p45,hs]

private theorem p47 : run 112451087 (some (5,0,1)) = some (0,15445,25193) := by
  have hp : path 1024 (0,19676,15533) = (4783414, some (0,15445,25193)) := by decide
  have hs : run 4783414 (some (0,19676,15533)) = some (0,15445,25193) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,19676,15533)
  have hc : run 112451087 (some (5,0,1)) = run 4783414 (run 107667673 (some (5,0,1))) := by
    simpa only [show 4783414 + 107667673 = 112451087 by decide] using run_add 4783414 107667673 (some (5,0,1))
  rw [hc,p46,hs]

private theorem p48 : run 117417041 (some (5,0,1)) = some (31416,12932,3) := by
  have hp : path 1024 (0,15445,25193) = (4965954, some (31416,12932,3)) := by decide
  have hs : run 4965954 (some (0,15445,25193)) = some (31416,12932,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,15445,25193)
  have hc : run 117417041 (some (5,0,1)) = run 4965954 (run 112451087 (some (5,0,1))) := by
    simpa only [show 4965954 + 112451087 = 117417041 by decide] using run_add 4965954 112451087 (some (5,0,1))
  rw [hc,p47,hs]

private theorem p49 : run 122327645 (some (5,0,1)) = some (0,23327,11817) := by
  have hp : path 1024 (31416,12932,3) = (4910604, some (0,23327,11817)) := by decide
  have hs : run 4910604 (some (31416,12932,3)) = some (0,23327,11817) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (31416,12932,3)
  have hc : run 122327645 (some (5,0,1)) = run 4910604 (run 117417041 (some (5,0,1))) := by
    simpa only [show 4910604 + 117417041 = 122327645 by decide] using run_add 4910604 117417041 (some (5,0,1))
  rw [hc,p48,hs]

private theorem p50 : run 127524713 (some (5,0,1)) = some (40112,9783,3) := by
  have hp : path 1024 (0,23327,11817) = (5197068, some (40112,9783,3)) := by decide
  have hs : run 5197068 (some (0,23327,11817)) = some (40112,9783,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,23327,11817)
  have hc : run 127524713 (some (5,0,1)) = run 5197068 (run 122327645 (some (5,0,1))) := by
    simpa only [show 5197068 + 122327645 = 127524713 by decide] using run_add 5197068 122327645 (some (5,0,1))
  rw [hc,p49,hs]

private theorem p51 : run 132791450 (some (5,0,1)) = some (15109,22894,0) := by
  have hp : path 1024 (40112,9783,3) = (5266737, some (15109,22894,0)) := by decide
  have hs : run 5266737 (some (40112,9783,3)) = some (15109,22894,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (40112,9783,3)
  have hc : run 132791450 (some (5,0,1)) = run 5266737 (run 127524713 (some (5,0,1))) := by
    simpa only [show 5266737 + 127524713 = 132791450 by decide] using run_add 5266737 127524713 (some (5,0,1))
  rw [hc,p50,hs]

private theorem p52 : run 137804184 (some (5,0,1)) = some (0,17060,27979) := by
  have hp : path 1024 (15109,22894,0) = (5012734, some (0,17060,27979)) := by decide
  have hs : run 5012734 (some (15109,22894,0)) = some (0,17060,27979) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (15109,22894,0)
  have hc : run 137804184 (some (5,0,1)) = run 5012734 (run 132791450 (some (5,0,1))) := by
    simpa only [show 5012734 + 132791450 = 137804184 by decide] using run_add 5012734 132791450 (some (5,0,1))
  rw [hc,p51,hs]

private theorem p53 : run 143295399 (some (5,0,1)) = some (18105,22598,0) := by
  have hp : path 1024 (0,17060,27979) = (5491215, some (18105,22598,0)) := by decide
  have hs : run 5491215 (some (0,17060,27979)) = some (18105,22598,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,17060,27979)
  have hc : run 143295399 (some (5,0,1)) = run 5491215 (run 137804184 (some (5,0,1))) := by
    simpa only [show 5491215 + 137804184 = 143295399 by decide] using run_add 5491215 137804184 (some (5,0,1))
  rw [hc,p52,hs]

private theorem p54 : run 148606983 (some (5,0,1)) = some (51767,6361,0) := by
  have hp : path 1024 (18105,22598,0) = (5311584, some (51767,6361,0)) := by decide
  have hs : run 5311584 (some (18105,22598,0)) = some (51767,6361,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (18105,22598,0)
  have hc : run 148606983 (some (5,0,1)) = run 5311584 (run 143295399 (some (5,0,1))) := by
    simpa only [show 5311584 + 143295399 = 148606983 by decide] using run_add 5311584 143295399 (some (5,0,1))
  rw [hc,p53,hs]

private theorem p55 : run 154473292 (some (5,0,1)) = some (0,18927,27835) := by
  have hp : path 1024 (51767,6361,0) = (5866309, some (0,18927,27835)) := by decide
  have hs : run 5866309 (some (51767,6361,0)) = some (0,18927,27835) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (51767,6361,0)
  have hc : run 154473292 (some (5,0,1)) = run 5866309 (run 148606983 (some (5,0,1))) := by
    simpa only [show 5866309 + 148606983 = 154473292 by decide] using run_add 5866309 148606983 (some (5,0,1))
  rw [hc,p54,hs]

private theorem p56 : run 159465132 (some (5,0,1)) = some (10186,28339,3) := by
  have hp : path 1024 (0,18927,27835) = (4991840, some (10186,28339,3)) := by decide
  have hs : run 4991840 (some (0,18927,27835)) = some (10186,28339,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,18927,27835)
  have hc : run 159465132 (some (5,0,1)) = run 4991840 (run 154473292 (some (5,0,1))) := by
    simpa only [show 4991840 + 154473292 = 159465132 by decide] using run_add 4991840 154473292 (some (5,0,1))
  rw [hc,p55,hs]

private theorem p57 : run 165256823 (some (5,0,1)) = some (0,8424,51227) := by
  have hp : path 1024 (10186,28339,3) = (5791691, some (0,8424,51227)) := by decide
  have hs : run 5791691 (some (10186,28339,3)) = some (0,8424,51227) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (10186,28339,3)
  have hc : run 165256823 (some (5,0,1)) = run 5791691 (run 159465132 (some (5,0,1))) := by
    simpa only [show 5791691 + 159465132 = 165256823 by decide] using run_add 5791691 159465132 (some (5,0,1))
  rw [hc,p56,hs]

private theorem p58 : run 171217408 (some (5,0,1)) = some (25613,21828,0) := by
  have hp : path 1024 (0,8424,51227) = (5960585, some (25613,21828,0)) := by decide
  have hs : run 5960585 (some (0,8424,51227)) = some (25613,21828,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,8424,51227)
  have hc : run 171217408 (some (5,0,1)) = run 5960585 (run 165256823 (some (5,0,1))) := by
    simpa only [show 5960585 + 165256823 = 171217408 by decide] using run_add 5960585 165256823 (some (5,0,1))
  rw [hc,p57,hs]

private theorem p59 : run 177079454 (some (5,0,1)) = some (0,30011,10447) := by
  have hp : path 1024 (25613,21828,0) = (5862046, some (0,30011,10447)) := by decide
  have hs : run 5862046 (some (25613,21828,0)) = some (0,30011,10447) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (25613,21828,0)
  have hc : run 177079454 (some (5,0,1)) = run 5862046 (run 171217408 (some (5,0,1))) := by
    simpa only [show 5862046 + 171217408 = 177079454 by decide] using run_add 5862046 171217408 (some (5,0,1))
  rw [hc,p58,hs]

private theorem p60 : run 183071644 (some (5,0,1)) = some (62962,4347,3) := by
  have hp : path 1024 (0,30011,10447) = (5992190, some (62962,4347,3)) := by decide
  have hs : run 5992190 (some (0,30011,10447)) = some (62962,4347,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,30011,10447)
  have hc : run 183071644 (some (5,0,1)) = run 5992190 (run 177079454 (some (5,0,1))) := by
    simpa only [show 5992190 + 177079454 = 183071644 by decide] using run_add 5992190 177079454 (some (5,0,1))
  rw [hc,p59,hs]

private theorem p61 : run 188734450 (some (5,0,1)) = some (0,17555,37725) := by
  have hp : path 1024 (62962,4347,3) = (5662806, some (0,17555,37725)) := by decide
  have hs : run 5662806 (some (62962,4347,3)) = some (0,17555,37725) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (62962,4347,3)
  have hc : run 188734450 (some (5,0,1)) = run 5662806 (run 183071644 (some (5,0,1))) := by
    simpa only [show 5662806 + 183071644 = 188734450 by decide] using run_add 5662806 183071644 (some (5,0,1))
  rw [hc,p60,hs]

private theorem p62 : run 194900961 (some (5,0,1)) = some (4769,34630,0) := by
  have hp : path 1024 (0,17555,37725) = (6166511, some (4769,34630,0)) := by decide
  have hs : run 6166511 (some (0,17555,37725)) = some (4769,34630,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,17555,37725)
  have hc : run 194900961 (some (5,0,1)) = run 6166511 (run 188734450 (some (5,0,1))) := by
    simpa only [show 6166511 + 188734450 = 194900961 by decide] using run_add 6166511 188734450 (some (5,0,1))
  rw [hc,p61,hs]

private theorem p63 : run 200992154 (some (5,0,1)) = some (0,19757,35719) := by
  have hp : path 1024 (4769,34630,0) = (6091193, some (0,19757,35719)) := by decide
  have hs : run 6091193 (some (4769,34630,0)) = some (0,19757,35719) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (4769,34630,0)
  have hc : run 200992154 (some (5,0,1)) = run 6091193 (run 194900961 (some (5,0,1))) := by
    simpa only [show 6091193 + 194900961 = 200992154 by decide] using run_add 6091193 194900961 (some (5,0,1))
  rw [hc,p62,hs]

private theorem p64 : run 207493337 (some (5,0,1)) = some (11098,32674,3) := by
  have hp : path 1024 (0,19757,35719) = (6501183, some (11098,32674,3)) := by decide
  have hs : run 6501183 (some (0,19757,35719)) = some (11098,32674,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,19757,35719)
  have hc : run 207493337 (some (5,0,1)) = run 6501183 (run 200992154 (some (5,0,1))) := by
    simpa only [show 6501183 + 200992154 = 207493337 by decide] using run_add 6501183 200992154 (some (5,0,1))
  rw [hc,p63,hs]

private theorem p65 : run 214500950 (some (5,0,1)) = some (15429,31111,0) := by
  have hp : path 1024 (11098,32674,3) = (7007613, some (15429,31111,0)) := by decide
  have hs : run 7007613 (some (11098,32674,3)) = some (15429,31111,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (11098,32674,3)
  have hc : run 214500950 (some (5,0,1)) = run 7007613 (run 207493337 (some (5,0,1))) := by
    simpa only [show 7007613 + 207493337 = 214500950 by decide] using run_add 7007613 207493337 (some (5,0,1))
  rw [hc,p64,hs]

private theorem p66 : run 221350081 (some (5,0,1)) = some (60450,9194,3) := by
  have hp : path 1024 (15429,31111,0) = (6849131, some (60450,9194,3)) := by decide
  have hs : run 6849131 (some (15429,31111,0)) = some (60450,9194,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (15429,31111,0)
  have hc : run 221350081 (some (5,0,1)) = run 6849131 (run 214500950 (some (5,0,1))) := by
    simpa only [show 6849131 + 214500950 = 221350081 by decide] using run_add 6849131 214500950 (some (5,0,1))
  rw [hc,p65,hs]

private theorem p67 : run 227927271 (some (5,0,1)) = some (0,17415,45195) := by
  have hp : path 1024 (60450,9194,3) = (6577190, some (0,17415,45195)) := by decide
  have hs : run 6577190 (some (60450,9194,3)) = some (0,17415,45195) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (60450,9194,3)
  have hc : run 227927271 (some (5,0,1)) = run 6577190 (run 221350081 (some (5,0,1))) := by
    simpa only [show 6577190 + 221350081 = 227927271 by decide] using run_add 6577190 221350081 (some (5,0,1))
  rw [hc,p66,hs]

private theorem p68 : run 234716247 (some (5,0,1)) = some (49137,16036,0) := by
  have hp : path 1024 (0,17415,45195) = (6788976, some (49137,16036,0)) := by decide
  have hs : run 6788976 (some (0,17415,45195)) = some (49137,16036,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,17415,45195)
  have hc : run 234716247 (some (5,0,1)) = run 6788976 (run 227927271 (some (5,0,1))) := by
    simpa only [show 6788976 + 227927271 = 234716247 by decide] using run_add 6788976 227927271 (some (5,0,1))
  rw [hc,p67,hs]

private theorem p69 : run 241246396 (some (5,0,1)) = some (0,26900,28595) := by
  have hp : path 1024 (49137,16036,0) = (6530149, some (0,26900,28595)) := by decide
  have hs : run 6530149 (some (49137,16036,0)) = some (0,26900,28595) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (49137,16036,0)
  have hc : run 241246396 (some (5,0,1)) = run 6530149 (run 234716247 (some (5,0,1))) := by
    simpa only [show 6530149 + 234716247 = 241246396 by decide] using run_add 6530149 234716247 (some (5,0,1))
  rw [hc,p68,hs]

private theorem p70 : run 248535103 (some (5,0,1)) = some (14996,34297,3) := by
  have hp : path 1024 (0,26900,28595) = (7288707, some (14996,34297,3)) := by decide
  have hs : run 7288707 (some (0,26900,28595)) = some (14996,34297,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,26900,28595)
  have hc : run 248535103 (some (5,0,1)) = run 7288707 (run 241246396 (some (5,0,1))) := by
    simpa only [show 7288707 + 241246396 = 248535103 by decide] using run_add 7288707 241246396 (some (5,0,1))
  rw [hc,p69,hs]

private theorem p71 : run 255156358 (some (5,0,1)) = some (0,34429,15909) := by
  have hp : path 1024 (14996,34297,3) = (6621255, some (0,34429,15909)) := by decide
  have hs : run 6621255 (some (14996,34297,3)) = some (0,34429,15909) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (14996,34297,3)
  have hc : run 255156358 (some (5,0,1)) = run 6621255 (run 248535103 (some (5,0,1))) := by
    simpa only [show 6621255 + 248535103 = 255156358 by decide] using run_add 6621255 248535103 (some (5,0,1))
  rw [hc,p70,hs]

private theorem p72 : run 262174224 (some (5,0,1)) = some (5783,40082,0) := by
  have hp : path 1024 (0,34429,15909) = (7017866, some (5783,40082,0)) := by decide
  have hs : run 7017866 (some (0,34429,15909)) = some (5783,40082,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,34429,15909)
  have hc : run 262174224 (some (5,0,1)) = run 7017866 (run 255156358 (some (5,0,1))) := by
    simpa only [show 7017866 + 255156358 = 262174224 by decide] using run_add 7017866 255156358 (some (5,0,1))
  rw [hc,p71,hs]

private theorem p73 : run 269741686 (some (5,0,1)) = some (63759,11698,0) := by
  have hp : path 1024 (5783,40082,0) = (7567462, some (63759,11698,0)) := by decide
  have hs : run 7567462 (some (5783,40082,0)) = some (63759,11698,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (5783,40082,0)
  have hc : run 269741686 (some (5,0,1)) = run 7567462 (run 262174224 (some (5,0,1))) := by
    simpa only [show 7567462 + 262174224 = 269741686 by decide] using run_add 7567462 262174224 (some (5,0,1))
  rw [hc,p72,hs]

private theorem p74 : run 277268194 (some (5,0,1)) = some (9180,39591,3) := by
  have hp : path 1024 (63759,11698,0) = (7526508, some (9180,39591,3)) := by decide
  have hs : run 7526508 (some (63759,11698,0)) = some (9180,39591,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (63759,11698,0)
  have hc : run 277268194 (some (5,0,1)) = run 7526508 (run 269741686 (some (5,0,1))) := by
    simpa only [show 7526508 + 269741686 = 277268194 by decide] using run_add 7526508 269741686 (some (5,0,1))
  rw [hc,p73,hs]

private theorem p75 : run 284925028 (some (5,0,1)) = some (0,34133,21289) := by
  have hp : path 1024 (9180,39591,3) = (7656834, some (0,34133,21289)) := by decide
  have hs : run 7656834 (some (9180,39591,3)) = some (0,34133,21289) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (9180,39591,3)
  have hc : run 284925028 (some (5,0,1)) = run 7656834 (run 277268194 (some (5,0,1))) := by
    simpa only [show 7656834 + 277268194 = 284925028 by decide] using run_add 7656834 277268194 (some (5,0,1))
  rw [hc,p74,hs]

private theorem p76 : run 292550530 (some (5,0,1)) = some (23932,33409,3) := by
  have hp : path 1024 (0,34133,21289) = (7625502, some (23932,33409,3)) := by decide
  have hs : run 7625502 (some (0,34133,21289)) = some (23932,33409,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,34133,21289)
  have hc : run 292550530 (some (5,0,1)) = run 7625502 (run 284925028 (some (5,0,1))) := by
    simpa only [show 7625502 + 284925028 = 292550530 by decide] using run_add 7625502 284925028 (some (5,0,1))
  rw [hc,p75,hs]

private theorem p77 : run 300160684 (some (5,0,1)) = some (37909,27022,0) := by
  have hp : path 1024 (23932,33409,3) = (7610154, some (37909,27022,0)) := by decide
  have hs : run 7610154 (some (23932,33409,3)) = some (37909,27022,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (23932,33409,3)
  have hc : run 300160684 (some (5,0,1)) = run 7610154 (run 292550530 (some (5,0,1))) := by
    simpa only [show 7610154 + 292550530 = 300160684 by decide] using run_add 7610154 292550530 (some (5,0,1))
  rw [hc,p76,hs]

private theorem p78 : run 308056227 (some (5,0,1)) = some (69005,12078,0) := by
  have hp : path 1024 (37909,27022,0) = (7895543, some (69005,12078,0)) := by decide
  have hs : run 7895543 (some (37909,27022,0)) = some (69005,12078,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (37909,27022,0)
  have hc : run 308056227 (some (5,0,1)) = run 7895543 (run 300160684 (some (5,0,1))) := by
    simpa only [show 7895543 + 300160684 = 308056227 by decide] using run_add 7895543 300160684 (some (5,0,1))
  rw [hc,p77,hs]

private theorem p79 : run 315743415 (some (5,0,1)) = some (0,16597,61159) := by
  have hp : path 1024 (69005,12078,0) = (7687188, some (0,16597,61159)) := by decide
  have hs : run 7687188 (some (69005,12078,0)) = some (0,16597,61159) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (69005,12078,0)
  have hc : run 315743415 (some (5,0,1)) = run 7687188 (run 308056227 (some (5,0,1))) := by
    simpa only [show 7687188 + 308056227 = 315743415 by decide] using run_add 7687188 308056227 (some (5,0,1))
  rw [hc,p78,hs]

private theorem p80 : run 323900244 (some (5,0,1)) = some (51575,21977,0) := by
  have hp : path 1024 (0,16597,61159) = (8156829, some (51575,21977,0)) := by decide
  have hs : run 8156829 (some (0,16597,61159)) = some (51575,21977,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,16597,61159)
  have hc : run 323900244 (some (5,0,1)) = run 8156829 (run 315743415 (some (5,0,1))) := by
    simpa only [show 8156829 + 315743415 = 323900244 by decide] using run_add 8156829 315743415 (some (5,0,1))
  rw [hc,p79,hs]

private theorem p81 : run 332951139 (some (5,0,1)) = some (22815,36961,0) := by
  have hp : path 1024 (51575,21977,0) = (9050895, some (22815,36961,0)) := by decide
  have hs : run 9050895 (some (51575,21977,0)) = some (22815,36961,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (51575,21977,0)
  have hc : run 332951139 (some (5,0,1)) = run 9050895 (run 323900244 (some (5,0,1))) := by
    simpa only [show 9050895 + 323900244 = 332951139 by decide] using run_add 9050895 323900244 (some (5,0,1))
  rw [hc,p80,hs]

private theorem p82 : run 341307318 (some (5,0,1)) = some (0,26980,43971) := by
  have hp : path 1024 (22815,36961,0) = (8356179, some (0,26980,43971)) := by decide
  have hs : run 8356179 (some (22815,36961,0)) = some (0,26980,43971) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (22815,36961,0)
  have hc : run 341307318 (some (5,0,1)) = run 8356179 (run 332951139 (some (5,0,1))) := by
    simpa only [show 8356179 + 332951139 = 341307318 by decide] using run_add 8356179 332951139 (some (5,0,1))
  rw [hc,p81,hs]

private theorem p83 : run 350119326 (some (5,0,1)) = some (84717,7210,0) := by
  have hp : path 1024 (0,26980,43971) = (8812008, some (84717,7210,0)) := by decide
  have hs : run 8812008 (some (0,26980,43971)) = some (84717,7210,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,26980,43971)
  have hc : run 350119326 (some (5,0,1)) = run 8812008 (run 341307318 (some (5,0,1))) := by
    simpa only [show 8812008 + 341307318 = 350119326 by decide] using run_add 8812008 341307318 (some (5,0,1))
  rw [hc,p82,hs]

private theorem p84 : run 359333831 (some (5,0,1)) = some (0,4455,91441) := by
  have hp : path 1024 (84717,7210,0) = (9214505, some (0,4455,91441)) := by decide
  have hs : run 9214505 (some (84717,7210,0)) = some (0,4455,91441) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (84717,7210,0)
  have hc : run 359333831 (some (5,0,1)) = run 9214505 (run 350119326 (some (5,0,1))) := by
    simpa only [show 9214505 + 350119326 = 359333831 by decide] using run_add 9214505 350119326 (some (5,0,1))
  rw [hc,p83,hs]

private theorem p85 : run 368101717 (some (5,0,1)) = some (0,43912,13713) := by
  have hp : path 1024 (0,4455,91441) = (8767886, some (0,43912,13713)) := by decide
  have hs : run 8767886 (some (0,4455,91441)) = some (0,43912,13713) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,4455,91441)
  have hc : run 368101717 (some (5,0,1)) = run 8767886 (run 359333831 (some (5,0,1))) := by
    simpa only [show 8767886 + 359333831 = 368101717 by decide] using run_add 8767886 359333831 (some (5,0,1))
  rw [hc,p84,hs]

private theorem p86 : run 376719439 (some (5,0,1)) = some (2159,50278,0) := by
  have hp : path 1024 (0,43912,13713) = (8617722, some (2159,50278,0)) := by decide
  have hs : run 8617722 (some (0,43912,13713)) = some (2159,50278,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,43912,13713)
  have hc : run 376719439 (some (5,0,1)) = run 8617722 (run 368101717 (some (5,0,1))) := by
    simpa only [show 8617722 + 368101717 = 376719439 by decide] using run_add 8617722 368101717 (some (5,0,1))
  rw [hc,p85,hs]

private theorem p87 : run 385229721 (some (5,0,1)) = some (39649,32126,0) := by
  have hp : path 1024 (2159,50278,0) = (8510282, some (39649,32126,0)) := by decide
  have hs : run 8510282 (some (2159,50278,0)) = some (39649,32126,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (2159,50278,0)
  have hc : run 385229721 (some (5,0,1)) = run 8510282 (run 376719439 (some (5,0,1))) := by
    simpa only [show 8510282 + 376719439 = 385229721 by decide] using run_add 8510282 376719439 (some (5,0,1))
  rw [hc,p86,hs]

private theorem p88 : run 394224191 (some (5,0,1)) = some (0,37923,29255) := by
  have hp : path 1024 (39649,32126,0) = (8994470, some (0,37923,29255)) := by decide
  have hs : run 8994470 (some (39649,32126,0)) = some (0,37923,29255) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (39649,32126,0)
  have hc : run 394224191 (some (5,0,1)) = run 8994470 (run 385229721 (some (5,0,1))) := by
    simpa only [show 8994470 + 385229721 = 394224191 by decide] using run_add 8994470 385229721 (some (5,0,1))
  rw [hc,p87,hs]

private theorem p89 : run 402968283 (some (5,0,1)) = some (69786,18245,3) := by
  have hp : path 1024 (0,37923,29255) = (8744092, some (69786,18245,3)) := by decide
  have hs : run 8744092 (some (0,37923,29255)) = some (69786,18245,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,37923,29255)
  have hc : run 402968283 (some (5,0,1)) = run 8744092 (run 394224191 (some (5,0,1))) := by
    simpa only [show 8744092 + 394224191 = 402968283 by decide] using run_add 8744092 394224191 (some (5,0,1))
  rw [hc,p88,hs]

private theorem p90 : run 412093756 (some (5,0,1)) = some (88162,9658,3) := by
  have hp : path 1024 (69786,18245,3) = (9125473, some (88162,9658,3)) := by decide
  have hs : run 9125473 (some (69786,18245,3)) = some (88162,9658,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (69786,18245,3)
  have hc : run 412093756 (some (5,0,1)) = run 9125473 (run 402968283 (some (5,0,1))) := by
    simpa only [show 9125473 + 402968283 = 412093756 by decide] using run_add 9125473 402968283 (some (5,0,1))
  rw [hc,p89,hs]

private theorem p91 : run 421177880 (some (5,0,1)) = some (0,1597,105465) := by
  have hp : path 1024 (88162,9658,3) = (9084124, some (0,1597,105465)) := by decide
  have hs : run 9084124 (some (88162,9658,3)) = some (0,1597,105465) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (88162,9658,3)
  have hc : run 421177880 (some (5,0,1)) = run 9084124 (run 412093756 (some (5,0,1))) := by
    simpa only [show 9084124 + 412093756 = 421177880 by decide] using run_add 9084124 412093756 (some (5,0,1))
  rw [hc,p90,hs]

private theorem p92 : run 430444019 (some (5,0,1)) = some (81438,14207,3) := by
  have hp : path 1024 (0,1597,105465) = (9266139, some (81438,14207,3)) := by decide
  have hs : run 9266139 (some (0,1597,105465)) = some (81438,14207,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,1597,105465)
  have hc : run 430444019 (some (5,0,1)) = run 9266139 (run 421177880 (some (5,0,1))) := by
    simpa only [show 9266139 + 421177880 = 430444019 by decide] using run_add 9266139 421177880 (some (5,0,1))
  rw [hc,p91,hs]

private theorem p93 : run 440328959 (some (5,0,1)) = some (47844,31607,3) := by
  have hp : path 1024 (81438,14207,3) = (9884940, some (47844,31607,3)) := by decide
  have hs : run 9884940 (some (81438,14207,3)) = some (47844,31607,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (81438,14207,3)
  have hc : run 440328959 (some (5,0,1)) = run 9884940 (run 430444019 (some (5,0,1))) := by
    simpa only [show 9884940 + 430444019 = 440328959 by decide] using run_add 9884940 430444019 (some (5,0,1))
  rw [hc,p92,hs]

private theorem p94 : run 449738109 (some (5,0,1)) = some (38503,36878,0) := by
  have hp : path 1024 (47844,31607,3) = (9409150, some (38503,36878,0)) := by decide
  have hs : run 9409150 (some (47844,31607,3)) = some (38503,36878,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (47844,31607,3)
  have hc : run 449738109 (some (5,0,1)) = run 9409150 (run 440328959 (some (5,0,1))) := by
    simpa only [show 9409150 + 440328959 = 449738109 by decide] using run_add 9409150 440328959 (some (5,0,1))
  rw [hc,p93,hs]

private theorem p95 : run 459360765 (some (5,0,1)) = some (56270,28591,3) := by
  have hp : path 1024 (38503,36878,0) = (9622656, some (56270,28591,3)) := by decide
  have hs : run 9622656 (some (38503,36878,0)) = some (56270,28591,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (38503,36878,0)
  have hc : run 459360765 (some (5,0,1)) = run 9622656 (run 449738109 (some (5,0,1))) := by
    simpa only [show 9622656 + 449738109 = 459360765 by decide] using run_add 9622656 449738109 (some (5,0,1))
  rw [hc,p94,hs]

private theorem p96 : run 468461603 (some (5,0,1)) = some (0,44767,25123) := by
  have hp : path 1024 (56270,28591,3) = (9100838, some (0,44767,25123)) := by decide
  have hs : run 9100838 (some (56270,28591,3)) = some (0,44767,25123) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (56270,28591,3)
  have hc : run 468461603 (some (5,0,1)) = run 9100838 (run 459360765 (some (5,0,1))) := by
    simpa only [show 9100838 + 459360765 = 468461603 by decide] using run_add 9100838 459360765 (some (5,0,1))
  rw [hc,p95,hs]

private theorem p97 : run 478590781 (some (5,0,1)) = some (98350,8754,3) := by
  have hp : path 1024 (0,44767,25123) = (10129178, some (98350,8754,3)) := by decide
  have hs : run 10129178 (some (0,44767,25123)) = some (98350,8754,3) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,44767,25123)
  have hc : run 478590781 (some (5,0,1)) = run 10129178 (run 468461603 (some (5,0,1))) := by
    simpa only [show 10129178 + 468461603 = 478590781 by decide] using run_add 10129178 468461603 (some (5,0,1))
  rw [hc,p96,hs]

private theorem p98 : run 488706794 (some (5,0,1)) = some (77091,19985,0) := by
  have hp : path 1024 (98350,8754,3) = (10116013, some (77091,19985,0)) := by decide
  have hs : run 10116013 (some (98350,8754,3)) = some (77091,19985,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (98350,8754,3)
  have hc : run 488706794 (some (5,0,1)) = run 10116013 (run 478590781 (some (5,0,1))) := by
    simpa only [show 10116013 + 478590781 = 488706794 by decide] using run_add 10116013 478590781 (some (5,0,1))
  rw [hc,p97,hs]

private theorem p99 : run 498922482 (some (5,0,1)) = some (0,12811,92643) := by
  have hp : path 1024 (77091,19985,0) = (10215688, some (0,12811,92643)) := by decide
  have hs : run 10215688 (some (77091,19985,0)) = some (0,12811,92643) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (77091,19985,0)
  have hc : run 498922482 (some (5,0,1)) = run 10215688 (run 488706794 (some (5,0,1))) := by
    simpa only [show 10215688 + 488706794 = 498922482 by decide] using run_add 10215688 488706794 (some (5,0,1))
  rw [hc,p98,hs]

private theorem p100 : run 509527672 (some (5,0,1)) = some (75409,22035,0) := by
  have hp : path 1024 (0,12811,92643) = (10605190, some (75409,22035,0)) := by decide
  have hs : run 10605190 (some (0,12811,92643)) = some (75409,22035,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,12811,92643)
  have hc : run 509527672 (some (5,0,1)) = run 10605190 (run 498922482 (some (5,0,1))) := by
    simpa only [show 10605190 + 498922482 = 509527672 by decide] using run_add 10605190 498922482 (some (5,0,1))
  rw [hc,p99,hs]

private theorem p101 : run 519895012 (some (5,0,1)) = some (0,9477,101721) := by
  have hp : path 1024 (75409,22035,0) = (10367340, some (0,9477,101721)) := by decide
  have hs : run 10367340 (some (75409,22035,0)) = some (0,9477,101721) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (75409,22035,0)
  have hc : run 519895012 (some (5,0,1)) = run 10367340 (run 509527672 (some (5,0,1))) := by
    simpa only [show 10367340 + 509527672 = 519895012 by decide] using run_add 10367340 509527672 (some (5,0,1))
  rw [hc,p100,hs]

private theorem p102 : run 530381207 (some (5,0,1)) = some (0,21981,77909) := by
  have hp : path 1024 (0,9477,101721) = (10486195, some (0,21981,77909)) := by decide
  have hs : run 10486195 (some (0,9477,101721)) = some (0,21981,77909) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,9477,101721)
  have hc : run 530381207 (some (5,0,1)) = run 10486195 (run 519895012 (some (5,0,1))) := by
    simpa only [show 10486195 + 519895012 = 530381207 by decide] using run_add 10486195 519895012 (some (5,0,1))
  rw [hc,p101,hs]

private theorem p103 : run 541185932 (some (5,0,1)) = some (118569,2262,0) := by
  have hp : path 1024 (0,21981,77909) = (10804725, some (118569,2262,0)) := by decide
  have hs : run 10804725 (some (0,21981,77909)) = some (118569,2262,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (0,21981,77909)
  have hc : run 541185932 (some (5,0,1)) = run 10804725 (run 530381207 (some (5,0,1))) := by
    simpa only [show 10804725 + 530381207 = 541185932 by decide] using run_add 10804725 530381207 (some (5,0,1))
  rw [hc,p102,hs]

private theorem p104 : run 552041396 (some (5,0,1)) = some (104197,10046,0) := by
  have hp : path 1024 (118569,2262,0) = (10855464, some (104197,10046,0)) := by decide
  have hs : run 10855464 (some (118569,2262,0)) = some (104197,10046,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (118569,2262,0)
  have hc : run 552041396 (some (5,0,1)) = run 10855464 (run 541185932 (some (5,0,1))) := by
    simpa only [show 10855464 + 541185932 = 552041396 by decide] using run_add 10855464 541185932 (some (5,0,1))
  rw [hc,p103,hs]

private theorem p105 : run 563272575 (some (5,0,1)) = some (72311,26600,0) := by
  have hp : path 1024 (104197,10046,0) = (11231179, some (72311,26600,0)) := by decide
  have hs : run 11231179 (some (104197,10046,0)) = some (72311,26600,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 1024 (104197,10046,0)
  have hc : run 563272575 (some (5,0,1)) = run 11231179 (run 552041396 (some (5,0,1))) := by
    simpa only [show 11231179 + 552041396 = 563272575 by decide] using run_add 11231179 552041396 (some (5,0,1))
  rw [hc,p104,hs]

private theorem p106 : run 567323514 (some (5,0,1)) = some (2,62973,0) := by
  have hp : path 366 (72311,26600,0) = (4050939, some (2,62973,0)) := by decide
  have hs : run 4050939 (some (72311,26600,0)) = some (2,62973,0) := by
    simpa only [hp,Prod.fst,Prod.snd] using path_sound 366 (72311,26600,0)
  have hc : run 567323514 (some (5,0,1)) = run 4050939 (run 563272575 (some (5,0,1))) := by
    simpa only [show 4050939 + 563272575 = 567323514 by decide] using run_add 4050939 563272575 (some (5,0,1))
  rw [hc,p105,hs]

/-- A nontrivial boundary state in the **actual** Machine C blank accelerator orbit.
    The Lean kernel checks 106 finite trace blocks, each of at most 1024 exact
    shortcut transitions. CJumpCore.run_sweep proves the exact equivalence
    between shortcut transitions and original accelerator calls. -/
theorem blank_reaches_a2_c0 :
    run 567323514 (some (5,0,1)) = some (2,62973,0) := p106
#print axioms blank_reaches_a2_c0
end BB6Agent38
