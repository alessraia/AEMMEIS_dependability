GestoreSedi<%@ page import="model.utenteService.Utente" %>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<html>
<head>
    <title>Admin HomePage</title>
    <link rel="stylesheet" type="text/css" href="./css/footerAdmin.css">
    <style>
        header {
            text-align: center;
            border-bottom-style: groove;
            padding: 10px;
        }
        body {
            justify-content: center;
            align-items: center;
            height: 100vh;
            margin: 0;
            font-family: Arial, sans-serif;
        }
        .contenitore {
            margin-top: 50px;
            text-align: center;
        }
        .iconAmm {
            margin: 20px;
        }
        .iconAmm img {
            margin: 0 auto;
        }
        .iconAmm a {
            display: block;
            margin-top: 10px;
            font-size: 20px;
            text-decoration: none;
            color: #000;
        }
        .iconAmm a:hover {
            color: #3a6977;
        }
        @media (max-width: 768px) {
            body {
                padding: 10px;
            }
            .iconAmm {
                margin: 10px;
            }
            .iconAmm img {
                height: auto;
            }
            .iconAmm a {
                font-size: 18px;
            }
        }
        @media (max-width: 480px) {
            .contenitore {
                padding: 10px;
            }
            .iconAmm {
                margin: 5px;
            }
            .iconAmm img {
                height: auto;
            }
            .iconAmm a {
                font-size: 16px;
            }
        }
    </style>
</head>
<body>
<%@include file="headerAdmin.jsp"%>
<div class="contenitore">
    <%
        String userType = ((Utente) session.getAttribute("utente")).getTipo();
    %>

    <% if ("GestoreCatalogo".equals(userType)) { %>
    <div class="iconAmm">
        <a href="gestisci-prodotti">
            <img src="./images/book-icon.png" alt="gestisci prodotti" width="50" height="50" class="image">
            <a href="gestisci-prodotti">Modifica Prodotti</a><br><br>
        </a>
    </div>
    <div class="iconAmm">
        <a href="gestisci-reparti">
            <img src="./images/elenco-icon.png" alt="gestisci reparti" width="60" height="70" class="image">
            <a href="gestisci-reparti"> Modifica Reparti </a><br><br>
        </a>
    </div>
    <% } else if ("GestoreSedi".equals(userType)) { %>
    <div class="iconAmm">
        <a href="gestisci-sedi">
            <img src="./images/sede-icon.png" alt="gestisci sedi" width="30" height="45" class="image">
            <a href="gestisci-sedi">Modifica Sedi</a><br><br>
        </a>
    </div>
    <% } else if ("GestoreOrdine".equals(userType)) { %>
    <div class="iconAmm">
        <a href="gestisci-ordini">
            <img src="./images/procurement.png" alt="gestisci ordini" width="48" height="50" class="image">
            <a href="gestici-ordini"> Modifica Ordini </a><br><br>
        </a>
    </div>
    <% } %>
</div>
<%@include file="/WEB-INF/results/footer.jsp"%>
</body>
</html>