1. File Strategy: 
    Option B
2. FIFO Type:
    Option A: register-based
3. FWFT:
    Let's try enabling FWFT first. If have timing issues, we can switch to Option B.
4. AR Issuing:
    Option A. We need NoC to serve as fast as possible.
5. Performance Tracking:
    All of above
6. Parallel Unpacking:
    It should be unaffected by the above changes. Keep it as is.

Answers to the questions:
1. Please see above
2. You can adjust the display messages according to your needs.
3. You can target conservative first. We will gradually iterate on the performance.
4. Ideally you should run all 10 tests. but you can start with one of ten to make sure it works. nevertheless, if you feel necessary, you can create a small benchmark just to make sure the back-to-back bursts work. Keep in mind our end goal is to have all 10 tests working.
5. Not only you should manually check the files and see if there are any hints, you also need to remember to check the document (not only this one) often when you are in doubt. 