# OBERON-TP
Compilateur Oberon écrit en Turbo Pascal basé sur le livre de "Compiler Construction" de Niklaus Wirth

<h3>Liste des unités</h3>

<table>
  <tr>
    <th>Nom</th>
    <th>Description</th>
  </tr>
  <tr>
      <td><b>OSG.PAS</b></td>
      <td>Cette unité contient le générateur de code assembleur du compilateur Oberon.</td>
  </tr>
	<tr>
     <td><b>OSS.PAS</b></b>
     <td>Cette unité contient l'analyseur du code source Oberon.</td>
  </tr>
	<tr>
    <td><b>RISC.PAS</b></td>
    <td>Cette unité contient l'exécuteur de code machine RISC.</td>
  </tr>
</table>

<h3>Liste des programmes</h3>

<table>
  <tr>
    <th>Nom</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><b>OSP.PAS</b></td>
    <td>Ce programme contient le compilateur Oberon. Il fait appel aux unités standard de Turbo Pascal et les 3 unités OSG, OSS et RISC fournit avec le projet.</td>
  </tr>
</table>
