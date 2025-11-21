<%--
  Created by IntelliJ IDEA.
  User: M.DELUCIA18
  Date: 15/05/2024
  Time: 10:05
  To change this template use File | Settings | File Templates.
--%>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<html>
<head>
    <title>Inserisci Libro</title>
    <link rel="stylesheet" type="text/css" href="css/formStyle2.css">
</head>
<body>
<div class="form">
    <h3>Nuovo Libro</h3>
    <div class="torna-indietro">
        <form action="gestisci-prodotti">
            <input type="submit" value="Torna indietro">
        </form>
    </div>
    <form action="insert-libro" method="post">
        <%String esito= (String) request.getAttribute("esito");
        if(esito!=null && esito.equals("non riuscito")){
            %>
        <p style="color: red">Libro già presente</p>
        <%}%>
        <label for="titolo">Titolo</label>
        <input type="text" id="titolo" name="titolo" required><br><br>

        <label for="isbn">Isbn</label>
        <input type="text" id="isbn" name="isbn" pattern="[0-9]{13}" required><br><br>

        <label for="genere">Genere</label>
        <input type="text" id="genere" name="genere" required><br><br>

        <label for="annoPubb">Anno Pubblicazione</label>
        <input type="text" id="annoPubb" name="annoPubb" pattern="[0-9]{4}" required
               title="Inserisci un anno di 4 cifre (es. 2024)"><br><br>

        <label for="prezzo">Prezzo</label>
        <input type="text"
               id="prezzo"
               name="prezzo"
               pattern="^(?!0$)([1-9][0-9]*|0\.[1-9][0-9]?|[1-9][0-9]*\.[0-9]{1,2})$"
               required
               title="Inserisci un prezzo maggiore di 0. Es: 0.01, 1, 10.50">
        <br><br>

        <label for="sconto">Sconto</label>
        <input type="text" id="sconto" name="sconto" pattern="[0-9]{0,3}" oninput="validateSconto()"><br><br>

        <label for="trama">Trama</label>
        <textarea id="trama" name="trama"></textarea><br><br>

        <label for="immagine">Immagine</label>
        <input type="text" id="immagine" name="immagine"><br>

        <div id="authors">
            <h4>Autori</h4>
            <div class="author">
                <label for="nome">Nome</label>
                <input type="text" id="nome" name="nome" required><br><br>
                <label for="cognome">Cognome</label>
                <input type="text" id="cognome" name="cognome" required><br><br>
                <label for="cf">Codice Fiscale</label>
                <input type="text"
                       id="cf"
                       name="cf"
                       pattern=^[A-Z0-9]{16}$
                       required
                       title="Inserisci un Codice Fiscale italiano valido (esattamente 16 caratteri in maiuscolo).">
            </div>
        </div>
        <button type="button" onclick="addAuthor()">
            <img src="images/add-icon3.png" alt="Menu" width="18" height="18"><br>
        </button>
        <br><br>
        <input type="submit" value="Inserisci">
    </form>
</div>

</body>

<script>
function addAuthor() {
    // Creazione di un nuovo div per il set di campi dell'autore
    var div = document.createElement('div');
    div.className = 'author';

    // Creazione dei campi di input per nome, cognome e codice fiscale
    div.innerHTML = `
    <label for="nome">Nome</label>
    <input type="text" id="nome" name="nome" required><br><br>
    <label for="cognome">Cognome</label>
    <input type="text" id="cognome" name="cognome" required><br><br>
    <label for="cf">Codice Fiscale</label>
    <input type="text"
           id="cf"
           name="cf"
           pattern="^(?:[A-Z][AEIOUX][AEIOUX]|[B-DF-HJ-NP-TV-Z]{2}[A-Z]){2}(?:[\dLMNP-V]{2}(?:[A-EHLMPR-T](?:[04LQ][1-9MNP-V]|[15MR][\dLMNP-V]|[26NS][0-8LMNP-U])|[DHPS][37PT][0L]|[ACELMRT][37PT][01LM]|[AC-EHLMPR-T][26NS][9V])|(?:[02468LNQSU][048LQU]|[13579MPRTV][26NS])B[26NS][9V])(?:[A-MZ][1-9MNP-V][\dLMNP-V]{2}|[A-M][0L](?:[1-9MNP-V][\dLMNP-V]|[0L][1-9MNP-V]))[A-Z]$"
           required
           title="Inserisci un Codice Fiscale italiano valido (esattamente 16 caratteri in maiuscolo).">
    <br><br>
    `;

    // Aggiunta del nuovo set di campi al div contenitore degli autori
    document.getElementById('authors').appendChild(div);
}
    function validateSconto() {
        var scontoInput = document.getElementById('sconto');
        var scontoValue = scontoInput.value.trim(); // Ottieni il valore e rimuovi spazi vuoti

        // Se il campo è vuoto, non fare alcuna validazione
        if (scontoValue === "") {
        scontoInput.setCustomValidity(""); // Nessun messaggio di errore
        return;
        }

        // Verifica se il valore è un numero valido tra 0 e 100
        var intValue = parseInt(scontoValue);
        if (isNaN(intValue) || intValue < 0 || intValue > 100) {
        scontoInput.setCustomValidity("Inserisci un numero valido tra 0 e 100.");
        } else {
            scontoInput.setCustomValidity(""); // Nessun messaggio di errore personalizzato
        }
    }
</script>
</html>
