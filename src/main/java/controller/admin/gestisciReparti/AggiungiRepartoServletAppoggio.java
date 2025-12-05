package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebServlet("/nuovo-reparto")
public class AggiungiRepartoServletAppoggio extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/reparti/aggiungiReparto.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward ", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }

}

