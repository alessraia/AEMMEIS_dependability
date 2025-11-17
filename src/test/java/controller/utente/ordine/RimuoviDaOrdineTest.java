package controller.utente.ordine;

import model.libroService.Libro;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.ordineService.RigaOrdine;
import model.utenteService.Utente;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

public class RimuoviDaOrdineTest {

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreRole");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);

        new RimuoviDaOrdine().doPost(request, response);

        verify(dispatcher, times(1)).forward(request, response);
        // Since servlet returns after forwarding, no further interactions expected
        verifyNoMoreInteractions(response);
    }

    @Test
    public void removeExistingRiga_iteratorRemovesAndRedirects() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("ISBN-1");
        when(request.getParameter("idOrdine")).thenReturn("ORD-1");

        // Prepare ordine with one riga matching isbn and idOrdine
        Libro libro = new Libro();
        libro.setIsbn("ISBN-1");

        RigaOrdine riga = new RigaOrdine();
        riga.setLibro(libro);
        riga.setIdOrdine("ORD-1");

        List<RigaOrdine> righe = new ArrayList<>();
        righe.add(riga);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine("ORD-1");
        ordine.setRigheOrdine(righe);

        // Mock OrdineDAO construction so doRetrieveById returns our ordine
        try (MockedConstruction<OrdineDAO> mocked = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD-1")).thenReturn(ordine))) {

            new RimuoviDaOrdine().doPost(request, response);

            // After removal, the list should be empty
            assertEquals(0, righe.size());
            verify(response, times(1)).sendRedirect("riepilogoOrdine.jsp");
        }
    }

    @Test
    public void whenIsbnNull_noRemoval_andRedirects() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn(null);
        when(request.getParameter("idOrdine")).thenReturn("ORD-2");

        // Prepare ordine with one riga
        Libro libro = new Libro();
        libro.setIsbn("SOME-ISBN");

        RigaOrdine riga = new RigaOrdine();
        riga.setLibro(libro);
        riga.setIdOrdine("ORD-2");

        List<RigaOrdine> righe = new ArrayList<>();
        righe.add(riga);

        Ordine ordine = new Ordine();
        ordine.setIdOrdine("ORD-2");
        ordine.setRigheOrdine(righe);

        try (MockedConstruction<OrdineDAO> mocked = mockConstruction(OrdineDAO.class,
                (mock, context) -> when(mock.doRetrieveById("ORD-2")).thenReturn(ordine))) {

            new RimuoviDaOrdine().doPost(request, response);

            // Since isbn was null, the list must remain unchanged
            assertEquals(1, righe.size());
            verify(response, times(1)).sendRedirect("riepilogoOrdine.jsp");
        }
    }
}
