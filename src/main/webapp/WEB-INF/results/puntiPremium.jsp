<%@ page import="model.tesseraService.Tessera" %>
<%@ page import="model.utenteService.Utente" %>
<%@ page import="model.tesseraService.TesseraDAO" %><%--
  Created by IntelliJ IDEA.
  User: aless
  Date: 05/01/2025
  Time: 16:53
  To change this template use File | Settings | File Templates.
--%>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>
<html>
<head>
    <title>Punti Tessera</title>
    <link rel="stylesheet" type="text/css" href="./css/generale.css">
    <link rel="stylesheet" type="text/css" href="./css/headerStyle.css">
    <link rel="stylesheet" type="text/css" href="./css/footerStyle.css">
    <link rel="stylesheet" type="text/css" href="css/formStyle2.css">
    <style>
        .form{
            margin:auto;
            margin-bottom: 15px;
        }

    </style>
</head>
<body>
<%@include file="header.jsp"%>
<div class="form">

    <% Utente utente = (Utente) session.getAttribute("utente");
        TesseraDAO tesseraDAO = new TesseraDAO();
        Tessera tessera = tesseraDAO.doRetrieveByEmail(utente.getEmail());
    %>
    <form action="punti-servlet">
        <div class="form-pag">
            <label for="punti">Vuoi sfruttare dei punti accumulati? (disponibili: <%=tessera.getPunti()%>)</label>
            <input type="text" id="punti" name="punti" data-max-punti="<%=tessera.getPunti()%>" oninput="aggiornaCosto()">
        </div>

        <div class="form-pag">
            <br><br><label for="costoAggiornato">Costo Aggiornato:</label>
            <span id="costoAggiornato">${ordine.costo}</span> €
        </div>

        <input type="hidden" id="costoIniziale" value="${ordine.costo}" name="costo">
        <input type="hidden" id="citta" value="${ordine.citta}" name="citta">
        <input type="hidden" id="indirizzoSpedizione" value="${ordine.indirizzoSpedizione}" name="indirizzo">

        <input type="submit" name="Vai al pagamento">
    </form>
</div>
<%@include file="footer.jsp"%>

<script>
    function aggiornaCosto() {
        let puntiInput = document.getElementById('punti');
        let punti = puntiInput.value;
        let maxPunti = parseInt(puntiInput.dataset.maxPunti);

        // Se il campo è vuoto, considera 0
        if (!punti) {
            punti = 0;
        }

        // Converti punti a intero
        var intValue = parseInt(punti);

        // Controlla validità
        if (isNaN(intValue) || intValue < 0 || intValue > maxPunti) {
            puntiInput.setCustomValidity("Inserisci un numero valido tra 0 e " + maxPunti);
        } else {
            puntiInput.setCustomValidity(""); // Nessun messaggio di errore personalizzato
        }
        let costoOrdine = document.getElementById('costoIniziale').value;
        let costoAggiornato = document.getElementById('costoAggiornato');
        let sconto = parseInt(punti) * 0.10; // Ogni punto vale 10 centesimi di euro
        let nuovoCosto = Math.max(0, parseFloat(costoOrdine) - sconto);
        costoAggiornato.innerHTML = nuovoCosto.toFixed(2); // Mostra il nuovo costo con due cifre decimali
    }
</script>
</body>
</html>
