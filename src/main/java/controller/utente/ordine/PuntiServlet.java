package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import model.ordineService.Ordine;
import model.utenteService.Utente;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.RoundingMode;

@WebServlet("/punti-servlet")
public class PuntiServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        String address = null;
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
            return;
        }
        Ordine ordine = new Ordine();
        ordine.setCitta(request.getParameter("citta"));
        ordine.setIndirizzoSpedizione(request.getParameter("indirizzo"));
        String puntiString = request.getParameter("punti");
        int punti = 0;
        if(puntiString != null && !puntiString.isEmpty())
            try {
                punti = Integer.parseInt(puntiString);
            }catch(NumberFormatException ex) {
                RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
                try {
                    dispatcher.forward(request, response);
                } catch (ServletException | IOException e) {
                    log("Errore durante il forward verso /WEB-INF/errorJsp/erroreForm.jsp", e);
                }
                return;
            }
        ordine.setPuntiSpesi(punti);

        String costoString = request.getParameter("costo");
        double costo;

        try {
            costo = Double.parseDouble(costoString);
        }catch(NumberFormatException ex) {
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/erroreForm.jsp", e);
            }
            return;
        }
        double costoAggiornato=costo - (ordine.getPuntiSpesi() * 0.10);
        BigDecimal bd = new BigDecimal(costoAggiornato).setScale(2, RoundingMode.HALF_UP);
        double costoArrotondato = bd.doubleValue();
        ordine.setCosto(costoArrotondato);

        address = "/WEB-INF/results/pagamentoOrdine.jsp";
        request.setAttribute("ordine", ordine);
        request.setAttribute("costo", request.getAttribute("costo"));
        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }
}
