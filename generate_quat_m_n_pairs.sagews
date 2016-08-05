︠dac6d1b7-6deb-4e8d-9be1-e29404efb536︠
num_vars = 2
sk = 0  # m value
test_skip = 1  # n value

miss_table = {}
good = []


def find_truant(qf):
    for i in range(2, 291):
        if qf.representation_vector_list(i+1)[i] == [] and i !=sk and i!=test_skip:
            return i
    print "Couldn't find truant?! Sorry..."
    
def generate_two_var_candidates():
    two_var_candidate_list = []
    T1 = 1 
    T2 = 2 if sk!=2 else 3
    if sk==1:
        T1=2
        T2=3
    if test_skip==3:
        T2 = 4
    if test_skip==2:
        T1=3
        T2=4
    print "Truant 1 is",T1,", Truant 2 is",T2
    for a in xrange(-int(sqrt(T1*T2)), int(sqrt(T1*T2))+1):
        #print a
        Q = QuadraticForm(ZZ, num_vars, [T1, 2*int(a), T2])
        if Q.is_positive_definite():
            rep_list = Q.representation_vector_list(test_skip+1)
            if rep_list[sk] == [] and rep_list[test_skip]==[]:
                two_var_candidate_list.append(Q)
    return two_var_candidate_list

def generate_three_var_candidates(c):
    T = find_truant(c)
    #print "Three var truant is", T
    three_var_candidate_list = []
    num_vars = 3
    old_coeffs = c.coefficients()
    center_term = old_coeffs[2]
    upper_left = old_coeffs[0]
    for b in xrange(-int(sqrt(center_term*T)), int(sqrt(center_term*T))+1):
        for a in xrange(-int(sqrt(upper_left*T)), int(sqrt(upper_left*T))+1):
            coeffs = [old_coeffs[0], old_coeffs[1], 2*int(a), old_coeffs[2], 2*int(b), T]
            Q = QuadraticForm(ZZ, num_vars, coeffs)
            if Q.is_positive_definite():
                rep_list = Q.representation_number_list(test_skip+1)
                if rep_list[sk]==0 and rep_list[test_skip]==0:
                    three_var_candidate_list.append(Q)
    return three_var_candidate_list

def generate_four_var_candidates(cand):
    T = find_truant(cand)
    #print "Four variable truant is", T
    four_var_candidate_list = []
    num_vars = 4
    old_coeffs = cand.coefficients()
    center_ul_term = old_coeffs[3]
    upper_left = old_coeffs[0]
    #print "\nupper_left=",upper_left,"T=",T,"center_ul_term=",center_ul_term,"old_coeffs=",old_coeffs
    for a in xrange(-int(sqrt(upper_left*T)), int(sqrt(upper_left*T))+1):
        for b in xrange(-int(sqrt(center_ul_term*T)), int(sqrt(center_ul_term*T))+1): 
            old_truant = old_coeffs[len(old_coeffs) - 1]
            for c in xrange(-int(sqrt(old_truant*T)), int(sqrt(old_truant*T))+1):
                coeffs = [old_coeffs[0], old_coeffs[1], old_coeffs[2], 2*a, old_coeffs[3], old_coeffs[4], 2*b, old_truant, 2*c, T]
                Q = QuadraticForm(ZZ, num_vars, coeffs)
                if Q.is_positive_definite():
                    rep_list = Q.representation_number_list(test_skip+1)
                    if rep_list[sk]==0 and rep_list[test_skip]==0:
                        four_var_candidate_list.append(Q)
    return four_var_candidate_list

def generate_m_n():
    ###### GENERATING TWO VARIABLE CANDIDATES ######
    two_var_candidate_list = generate_two_var_candidates()
    print "DONE WITH TWO VARIABLE CANDIDATES"
    for form in two_var_candidate_list:
        print form, find_truant(form)

    ###### GENERATING THREE VARIABLE CANDIDATES ######
    three_var_candidate_list = []

    for c in two_var_candidate_list:
        three_var_candidate_list += generate_three_var_candidates(c)

    #print len(three_var_candidate_list), "three var candidates"

    if len(three_var_candidate_list) > 0:

        uniq_three_vars = [three_var_candidate_list[0]]

        while len(three_var_candidate_list) > 1:
            before_len = len(three_var_candidate_list)
            old_coeffs = three_var_candidate_list[0].coefficients()
            three_var_candidate_list = filter(lambda x: not three_var_candidate_list[0].is_globally_equivalent_to(x), three_var_candidate_list[1:])
            #print "We found %d qfs that are equivalent to" % (before_len - len(three_var_candidate_list)), old_coeffs
            if len(three_var_candidate_list) > 0:
                uniq_three_vars.append( three_var_candidate_list[0])

        print "DONE WITH GENERATING THREE VARIABLE CANDIDATES"

        ###### GENERATING FOUR VARIABLE CANDIDATES #######

        four_var_candidate_list = []

        for i in range(len(uniq_three_vars)):
            three_var = uniq_three_vars[i]
            #print "Escalating from three var form #%d" % i
            four_var_candidate_list += generate_four_var_candidates(three_var)

        pos_four_vars = four_var_candidate_list
        len(pos_four_vars)

        good = []
        for x in pos_four_vars:
            if x.representation_number_list(100).count(0)<3:
                good.append(x)
        #print "len(good)=%d" % len(good)

        for x in pos_four_vars:
            if x.matrix().determinant() == 0:
                print "The form", x.coefficients(), "has a zero determinant"

        if len(good) > 0:
            uniq_four_vars = [good[0]]

            while len(good) > 1:
                before_len = len(good)
                old_coeffs = good[0].coefficients()
                good = filter(lambda x: not good[0].is_globally_equivalent_to(x), good[1:])
                #print "We found %d qfs that are equivalent to" % (before_len - len(good)), old_coeffs
                if len(good) > 0:
                    uniq_four_vars.append(good[0])

            print "Now we have %d unique four variable forms for {%d,%d}" % (len(uniq_four_vars), sk, test_skip)


            '''count0 = []
            for x in uniq_four_vars:
                count0.append(x.representation_number_list(1000).count(0)) '''

            for x in uniq_four_vars:
                rep_list = x.representation_number_list(10000)
                num = rep_list.count(0)
                if num in miss_table:
                    miss_table[num].append((x, sk+1+rep_list[sk:].index(0))) # the form and the truant greater than sk
                else:
                    miss_table[num] = [(x, sk+1+rep_list[sk:].index(0))]
                    
            if 2 in miss_table and len(miss_table[2]) > 0:
                print "We found %d forms potentially missing %d and %d\n\n" % (len(miss_table[2]), sk, test_skip)
                ##### uncomment the line below if you want to export the data to a file in Gram matrix format
                '''filename="miss_%d_%d.txt" % (sk, test_skip)
                with open(filename, "w") as f:
                    for form in miss_table[2]:
                        matrix = form[0].Gram_matrix()
                        line = str(matrix[0])[1:-1] + ", "
                        line += str(matrix[1][1:])[1:-1] + ", "
                        line += str(matrix[2][2:])[1:-1] + ", "
                        line += str(matrix[3][3])
                        f.write(line)
                        f.write("\n")''' 
        else:
            print "No four variable forms found for {%d,%d}\n" % (sk,test_skip)
    else:
        print "No three variable forms found for {%d,%d}\n" % (sk,test_skip)
        
biggest = {14:78, 10:58, 7:55, 5:35, 3:39, 2:38, 1:41, 6:15} 
for sk in [1, 2, 3, 5, 6, 7, 10, 14]:
    for test_skip in xrange(sk+1,biggest[sk]+1):
        generate_m_n()
    print "\n-----------\n"










