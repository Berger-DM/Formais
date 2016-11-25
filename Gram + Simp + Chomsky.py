# coding: utf-8
import collections
from collections import defaultdict
import copy
# Variáveis Globais


smbls = []
rgrs = collections.OrderedDict()
vrvs = []
trmns = []
vistos = []

nope = ['\t', '\n', '#']
nope1 = [' ', ']']

smbls.append([])
smbls.append([])
smbls.append([])
smbls.append(rgrs)


def get_gramatica():
    global rgrs
    z = -1
    with open('gramatica.txt', 'a') as file:
        file.write('\t')

    with open('gramatica.txt') as file:
        for line in file:
            if line[0] == '#':
                i = 0
                x = ''
                aux = ''
                while x not in nope:
                    aux += x
                    i += 1
                    x = line[i]
                if aux == 'Terminais':
                    z = 0
                elif aux == 'Variaveis':
                    z = 1
                elif aux == 'Inicial':
                    z = 2
                elif aux == 'Regras':
                    z = 3
                else:
                    pass
            elif line[0] == '[':
                x = ' '
                aux = ''
                i = 0
                while x == ' ':
                    i += 1
                    x = line[i]
                while x not in nope1:
                    aux += x
                    i += 1
                    x = line[i]
                if z != 3:
                    smbls[z].append(aux)
                if z == 1:
                    smbls[3][aux] = []
                elif z == 2:
                    rgrs = smbls[3]
                elif z == 3:
                    y = aux
                    aux = ''
                    x = ''
                    while x not in nope:
                        x = line[i]
                        if x.isalnum():
                            aux += x
                        i += 1
                    rgrs[y].append(aux)

    global trmns
    trmns = smbls[0]
    global vrvs
    vrvs = smbls[1]
    init = smbls[2]
    global inicial
    inicial = init[0]

    rgrs.move_to_end(inicial, last=False)

    qtrpl = 'G = ({'
    saux = ', '.join(e for e in vrvs)
    qtrpl += saux + '},{'
    saux = ', '.join(e for e in trmns)
    qtrpl += saux + '},P,' + init[0] + ')'
    print('Gramática Encontrada.')
    print(qtrpl)
    print('Com P = {')
    for j in rgrs:
        print(j + ' -> ' + '| '.join(e for e in rgrs[j]))
    print('}')

    return 0


def derivacoes_vazias(regras):
    """Etapa: exclusao de producoes vazias. Encontra as variaveis que levam a producoes vazias
    direta ou indiretamente"""
    aux_list = []
    vazio = []
    ind = -1
    flag = 0

    # Variaveis que derivam palavra vazia diretamente  
    for j in regras:
        for e in regras[j]:
            if e == 'V':
                flag = 1  # flag para marcar se há derivacao para vazio
                vazio.append(j)
            else:
                aux_list.append(e)

        # se houver, retira o vazio
        if flag == 1:
            del regras[j][:]
            for i in aux_list:
                rgrs[j].append(i)
            flag = 0
        del aux_list[:]

    # Variaveis que derivam palavra vazia indiretamente      
    for v in vazio:
        for j in rgrs:
            for e in rgrs[j]:
                if v in e and j not in vazio:
                    vazio.append(j)
                else:
                    pass

    for a in vazio:
        print(a)
    return vazio


def trocar_producoes(regras, vazio):
    """Etapa: exclusao de producoes vazias. Troca as variaveis que levam a producao vazia por suas combinacoes
       e adiciona producao vazia a variavel inicial, se necessario."""
    ind = -1
    for j in regras:
        for v in vazio:
            for e in regras[j]:
                ind += 1
                if v in e:
                    aux = v
                    aux2 = regras[j][ind]
                    aux2 = aux2.replace(aux, "")  # exclui a substring contida em aux
                    if aux2 != '' and aux2 not in regras[j]:
                        regras[j].append(aux2)
                    else:
                        pass

                    # adiciona producao vazia a variavel inicial
                    if aux2 == '' and j == inicial and 'V' not in regras[j]:
                        regras[j].append('V')
            ind = -1
    return 0


def fecho_transitivo(regras):
    """Etapa: exclusao de producoes simples. Cria fecho transitivo"""
    fecho = defaultdict(list)
    aux_list = []
    ind = -1
    ind2 = -1

    # variaveis unitarias diretas
    for j in regras:
        for e in regras[j]:
            for a in vrvs:
                if e == a:
                    fecho[j].append(a)
                else:
                    pass

    # variaveis unitarias indiretas
    fecho_aux = fecho
    for f in fecho:
        for k in fecho[f]:
            for b in fecho_aux:
                if k == b:
                    for c in fecho_aux[b]:
                        if c not in fecho[f]:
                            regras[f].append(c)

    # substitui as producoes A -> B por A -> alfa
    for j in regras:
        for e in regras[j]:
            if e in vrvs:
                for k in regras[e]:
                    if k not in vrvs and k not in aux_list:
                        aux_list.append(k)

            elif e not in aux_list:
                aux_list.append(e)

        del regras[j][:]
        for i in aux_list:
            regras[j].append(i)
        del aux_list[:]
    return 0


def vrvs_inacessiveis(regras):
    """Etapa: exclusao de producoes inuteis. Exclui variaveis nao alcancadas
    a partir do simbolo inicial"""
    vrvs_acess = []
    vrvs_no_acess = []

    vrvs_acess.append(inicial)

    # variaveis alcancadas
    for va in vrvs_acess:
        for e in regras[va]:
            for v in vrvs:
                if v in e and v not in vrvs_acess:
                    vrvs_acess.append(v)

    # variaveis nao alcancadas
    for v in vrvs:
        if v not in vrvs_acess:
            vrvs_no_acess.append(v)

    # modificacao nas regras
    for vna in vrvs_no_acess:
        regras.pop(vna, None)

    return 0


def dlt_useless_prod(k, prds, dct):
    lst = dct[k]
    for i in prds:
        lst.remove(i)
    dct[k] = lst


def path(dct, smbl, reached):
    rchd = reached
    past = copy.deepcopy(rchd)
    past.remove(smbl)
    for i in range(len(dct[smbl])):
        for k in vrvs:
            if k in dct[smbl][i]:
                if k not in rchd:
                    rchd.add(k)
                else:
                    return rchd
    for j in rchd:
        path(dct, j, rchd)
    return rchd


def nao_derivam_trmns(regras):
    """Etapa: exclusao de producoes inuteis. Exclui producoes com variaveis que nao derivam
    uma cadeia de terminais, direta ou indiretamente"""
    # print(regras)
    to_xcld = -1
    flags = {}
    grntd = []
    dltd = []
    xdict = regras
    for key, value in xdict.items():
        flags[key] = -1
    # cria flags pra saber se vai diretamente pra um terminal isolado ou não
    for key, value in xdict.items():
        for j in range(len(xdict[key])):
            if xdict[key][j] in trmns:
                flags[key] = 1
                grntd.append(key)
    # marca os flags apropriados e remove de uma lista auxiliar de variáveis as que alcançam diretamente
    vrs = copy.deepcopy(vrvs)
    vrs.reverse()
    for elem in grntd:
        try:
            vrs.remove(elem)
        except:
            pass
    # print(vrs)

    for key, value in xdict.items():
        xcld = -1
        for j in range(len(xdict[key])):
            if key not in xdict[key][j]:
                xcld = 1
                # print(key + " " + str(xcld))
        if xcld == -1:
            # mesmo depois de todas a iterações necessárias não chegou em nada além dele próprio, é loop, remove
            dltd.append(key)
            del xdict[key]

    for key, value in xdict.items():
        aux_lst = []
        for j in range(len(xdict[key])):
            for k in dltd:
                if k in xdict[key][j]:
                    aux_lst.append(xdict[key][j])
        dlt_useless_prod(key, aux_lst, xdict)  # remove produções que continham as variáveis em loop
        if not xdict[key]:  # verifica se ficou alguma variável sem produção por causa da remoção das inúteis
            del xdict[key]  # eram parte do loop e são removidas também

    if dltd:  # verifica o dicionário quantas vezes for necessário pra garantir que nenhuma produção inútil restou
        nao_derivam_trmns(xdict)

    st = set()  # etapa 2 das produções inuteis - variáveis inalcançaveis
    st.add('S')
    reach = path(xdict, 'S', st)
    for key, value in xdict.items():
        if key not in reach:  # se não for alcançada a partir do inicial, é removida
            del xdict[key]  # e como não estava em nenhuma produção efetiva não há preocupação com o resto.


def chomsky(regras):
    new_vars = {}
    trmns_auxs = []
    tamanhos = dict()
    index = -1
    for t in trmns:
        tamanhos[t] = len(t)

    for j in regras:
        for e in regras[j]:
            index += 1
            for t in trmns:
                if t == e:  # se for um terminal sozinho
                    pass
                elif t in e:  # terminal nao sozinho

                    ind = e.find(t)  # acha a primeira posicao do terminal

                    for tam in tamanhos:
                        auxi = int(tamanhos[tam])
                        auxj = int(tamanhos[t])

                        if e[ind:ind + auxi] in trmns and auxi != auxj:  # testa se é uma substring de outro terminal
                            pass

                        else:
                            aux = e[:ind] + 'T' + e[ind:]  # acrescenta 'T' antes do terminal para criar nova variavel
                            regras[j][index] = e.replace(e, aux)  # substitui terminal  pela nova variavel
                            aux2 = 'T' + t
                            print(aux2)

                            if aux2 not in vrvs:  # atualiza a gramatica
                                vrvs.append(aux2)

                            if t not in trmns_auxs:  # novos terminais a serem adicionados as regras
                                trmns_auxs.append(t)
                            regras[aux2] = []
                            regras[aux2].append(t)
        index = -1

    num_new_vars = 0
    for key, value in regras.items():
        for i in range(len(regras[key])):
            count = 0
            for k in vrvs:
                if k in regras[key][i]:
                    count += 1
                    if regras[key][i].count(k) > 1:
                        count += 1
            if count > 2:
                print(regras[key][i])
                lista_switch = []
                for k in vrvs:
                    if k in regras[key][i]:
                        if regras[key][i].startswith(k):
                            lista_switch.append(k)
                            aux = copy.copy(regras[key][i])
                            aux = aux.replace(k, '')
                            for l in vrvs:
                                if aux.startswith(l):
                                    lista_switch.append(l)
                combo = lista_switch[0] + lista_switch[1]
                print(combo)
                if combo in new_vars.values():
                    print('já existe uma variavel para esta combinação')
                else:
                    num_new_vars += 1
                    nv = 'X' + str(num_new_vars)
                    new_vars[nv] = combo
    # print(new_vars)
    new_vars = collections.OrderedDict(sorted(new_vars.items(), key=lambda t: t[0]))
    for vr, cmb in new_vars.items():
        for key in regras.keys():
            for each in range(len(regras[key])):
                # print(cmb + " " + regras[key][each])
                if cmb in regras[key][each]:
                    # print('troca')
                    regras[key][each] = regras[key][each].replace(cmb, vr)
        vrvs.append(vr)
        regras[vr] = []
        regras[vr].append(cmb)

    return 0


def printa1(rgrs):
    print('\nProducao apos etapa 1:')
    print('Com P\' = {')
    for j in rgrs:
        print(j + ' -> ' + '| '.join(e for e in rgrs[j]))
    print('}')
    return 0


def printa2(rgrs):
    print('\nProducao apos Chomsky:')
    qtrpl = 'G = ({'
    saux = ', '.join(e for e in vrvs)
    qtrpl += saux + '},{'
    saux = ', '.join(e for e in trmns)
    qtrpl += saux + '},P,' + inicial + ')'
    print('Gramática Encontrada.')
    print(qtrpl)
    print('Com P = {')
    for j in rgrs:
        print(j + ' -> ' + '| '.join(e for e in rgrs[j]))
    print('}')
    return 0


get_gramatica()
vazio = derivacoes_vazias(rgrs)
trocar_producoes(rgrs, vazio)
printa1(rgrs)
fecho_transitivo(rgrs)
# aux_dict = copy.deepcopy(rgrs)
nao_derivam_trmns(rgrs)
for i in rgrs:
    print(i + ": " + str(rgrs[i]))
chomsky(rgrs)
printa2(rgrs)
